import Foundation.Constructions.Symmetric.RandomFunctionMACNativeCaller
import Foundation.Crypto.Semantics.Oracle.NativeDeterministic
import Foundation.Crypto.Semantics.Oracle.NativeFixedResponse
import Foundation.Crypto.Semantics.Oracle.NativeCopyBlock

/-! Stage verification for the concrete MAC caller. All stages use the same
251-instruction code and the original timed interactive transition system.
The complete four-call correctness/halting theorem is not assumed here.
-/
namespace Foundation.Symmetric.RandomFunctionMACNativeCaller.Native
open Foundation.Probability CryptoOracle CryptoOracle.Interactive TimedExecution Machine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def afterCoin (coin : Bool) : Machine.Configuration :=
  { pc := 1, inputTape := {current := some coin} }

def firstCall (coin : Bool) : Machine.Configuration :=
  { pc := 15, inputTape := {current := some coin},
    outputTape := RequestExport.packetTape [] [] (encodeMessage (firstMessage coin)) }

/-- This checks actual instruction fetching and tape moves, not a host-built
request treated as an executed machine operation. The native run is 12 steps
after the one random instruction; both coin choices are checked. -/
theorem first_setup_checked (coin : Bool) :
    NativeDeterministic.run code 12 (afterCoin coin) = some (firstCall coin) := by
  cases coin <;> decide_cbv

theorem first_setup_native {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) :
    TimedExecution.eval (Reification.timedStep code oracle) 12
      (⟨state, .running (afterCoin coin), trace⟩ : Configuration State) =
    PMF.pure ⟨state, .running (firstCall coin), trace⟩ :=
  NativeDeterministic.run_sound code oracle state trace 12 (afterCoin coin) (firstCall coin)
    (first_setup_checked coin)

theorem initial_step {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) :
    Reification.timedStep code oracle (⟨state, .running {}, trace⟩ : Configuration State) =
      sampleBit.map (fun coin => ⟨state, .running (afterCoin coin), trace⟩) := by
  simp only [Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
    transition, code, List.cons_append, List.nil_append, List.getElem?_cons_zero,
    Machine.Instruction.next, Machine.Configuration.updateTape, Machine.Configuration.advance,
    Bool.false_eq_true, if_false]
  congr 1
  funext coin
  cases coin <;> rfl

/-- Local randomness and the first request's physical construction take
exactly thirteen transitions, preserving arbitrary prior oracle state/trace. -/
theorem first_setup {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (Reification.timedStep code oracle) 13
      (⟨state, .running {}, trace⟩ : Configuration State) =
      sampleBit.map (fun coin => ⟨state, .running (firstCall coin), trace⟩) := by
  rw [TimedExecution.eval, initial_step, PMF.bind_map]
  change (sampleBit.bind (fun coin => TimedExecution.eval (Reification.timedStep code oracle) 12
    (⟨state, .running (afterCoin coin), trace⟩ : Configuration State))) = _
  simp only [first_setup_native]
  rfl

theorem first_call_position (coin : Bool) : code[(firstCall coin).pc]? = some .call := by decide_cbv

/-- The first full exchange costs 36 transitions for a three-bit request and
eight-bit response, including actual export/loading and caller resumption. -/
theorem first_transfer {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 36
      (⟨state, .running (firstCall coin), trace⟩ : Configuration State) =
      (packetOracle world state (encodeMessage (firstMessage coin))).map
        (QueryTransfer.resumed (firstCall coin).advance trace (encodeMessage (firstMessage coin))) := by
  have law := QueryTransfer.fixed_response_call code (packetOracle world) (firstCall coin)
    state trace (encodeMessage (firstMessage coin)) [] [] rfl (first_call_position coin) rfl 8
    (packet_response_width world state (encodeMessage (firstMessage coin)))
  simpa only [message_width] using law

/-- A single continuing run reaches the first returned response in exactly
49 transitions. The logical outcome retains the entire actual caller frame,
opaque oracle state and full preceding/current transcript. -/
theorem first_query_run {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 49
      (⟨state, .running {}, trace⟩ : Configuration State) =
      sampleBit.bind (fun coin =>
        (packetOracle world state (encodeMessage (firstMessage coin))).map
          (QueryTransfer.resumed (firstCall coin).advance trace (encodeMessage (firstMessage coin)))) := by
  rw [show 49 = 13 + 36 by rfl, TimedExecution.eval_add, first_setup, PMF.bind_map]
  congr 1
  funext coin
  exact first_transfer world state trace coin

/-- Both byte-saving sites contain eight instances of the verified native
copy block. These obligations concern the fetched code, not an abstract byte
operation or an externally supplied machine-realization assumption. -/
theorem copy_locations (third : Bool) (index : Fin 8) :
    NativeCopyBlock.Located code ((if third then 122 else 32) + 7 * index.val) 249 := by
  fin_cases index <;> cases third <;> constructor <;> decide_cbv

theorem saved_bit_run {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (third : Bool) (index : Fin 8)
    (destination : Tape) (left right : List (Option Bool)) (bit : Bool) :
    TimedExecution.eval (Reification.timedStep code oracle) 5
      (⟨state, .running (NativeCopyBlock.start ((if third then 122 else 32) + 7 * index.val)
        destination left right bit), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (NativeCopyBlock.finish ((if third then 122 else 32) + 7 * index.val)
        destination left right bit), trace⟩ :=
  NativeCopyBlock.timed code oracle _ 249 (copy_locations third index) destination left right bit state trace

/-- All eight response bits are copied by actual native instructions in
forty transitions, for every tag and arbitrary existing caller memory. The
final memory/head layout is retained for the subsequent physical rewind. -/
theorem saved_tag_bits_run {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (third : Bool) (destination : Tape) (tag : Tag) :
    TimedExecution.eval (Reification.timedStep code oracle) 40
      (⟨state, .running (NativeCopyBlock.manyStart (if third then 122 else 32)
        destination [] [] (encodeTag tag)), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (NativeCopyBlock.manyFinish (if third then 122 else 32)
        destination [] [] (encodeTag tag)), trace⟩ := by
  have located : ∀ index, index < (encodeTag tag).length →
      NativeCopyBlock.Located code ((if third then 122 else 32) + 7 * index) 249 := by
    intro index inside
    exact copy_locations third ⟨index, by simpa only [tag_width] using inside⟩
  simpa only [tag_width, Nat.reduceMul] using NativeCopyBlock.many_timed code oracle
    (if third then 122 else 32) 249 destination [] [] (encodeTag tag) located state trace

end Foundation.Symmetric.RandomFunctionMACNativeCaller.Native
