import Foundation.Constructions.Symmetric.RandomFunctionMACNativeOptimizedExecution
import Foundation.Constructions.Symmetric.RandomFunctionMACNativeRequests

/-! Complete native-frame refinement, not just output-bit equivalence.
Final counters relocate by one instruction; every tape, oracle state and
request/response history is retained. Prefix formats cover actual requests. -/
namespace Foundation.Symmetric.RandomFunctionMACNativeOptimized
open Foundation.Probability CryptoOracle CryptoOracle.Interactive TimedExecution Machine
open RandomFunctionMACNativeCaller
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def shiftPC (machine : Machine.Configuration) : Machine.Configuration := {machine with pc := machine.pc + 1}

theorem compare_result_shift (base reject : Nat)
    (inputLeft outputLeft inputAfter outputAfter : List (Option Bool)) (pairs : List (Bool × Bool)) :
    NativeCompareBlock.result (base + 1) (reject + 1) inputLeft outputLeft inputAfter outputAfter pairs =
      (shiftPC (NativeCompareBlock.result base reject inputLeft outputLeft inputAfter outputAfter pairs).1,
        (NativeCompareBlock.result base reject inputLeft outputLeft inputAfter outputAfter pairs).2) := by
  induction pairs generalizing base inputLeft outputLeft with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨first, second⟩
      by_cases same : first = second
      · simp only [NativeCompareBlock.result, if_pos same]
        rw [show base + 1 + 5 = (base + 5) + 1 by omega]
        exact congrArg (fun result : Machine.Configuration × Nat => (result.1, 4 + result.2))
          (ih (base + 5) (some first :: inputLeft) (some second :: outputLeft))
      · simp only [NativeCompareBlock.result, if_neg same]
        rfl

theorem comparison_result_shift (coin : Bool) (candidate actual : Tag) :
    comparisonResult coin candidate actual =
      (shiftPC (RandomFunctionMACNativeCaller.Native.comparisonResult coin candidate actual).1,
        (RandomFunctionMACNativeCaller.Native.comparisonResult coin candidate actual).2) :=
  compare_result_shift 207 249 [some coin] [] [] [] (RandomFunctionMACNativeCaller.Native.comparisonPairs candidate actual)

def relocate {State : Type} (frame : Configuration State) : Configuration State :=
  {frame with control := match frame.control with | .running machine => .running (shiftPC machine) | other => other}

theorem executionLaw_refinement {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) :
    (RandomFunctionMACNativeCaller.Native.executionLaw world state trace coin).map relocate =
      executionLaw world state trace coin := by
  simp only [RandomFunctionMACNativeCaller.Native.executionLaw, executionLaw, PMF.map_bind,
    PMF.map_comp, Function.comp_def, comparison_result_shift, relocate]

theorem whole_frame_refinement {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) :
    (TimedExecution.eval (Reification.timedStep RandomFunctionMACNativeCaller.Native.code (packetOracle world)) 343
      (⟨state, .running {}, trace⟩ : Configuration State)).map relocate =
      TimedExecution.eval (Reification.timedStep code (packetOracle world)) 286
        (⟨state, .running {}, trace⟩ : Configuration State) := by
  rw [RandomFunctionMACNativeCaller.Native.whole_run, whole_run, PMF.map_bind]
  apply congrArg (fun continuation => sampleBit.bind continuation)
  funext coin
  exact executionLaw_refinement world state trace coin

theorem observe_relocate {State : Type} (frame : Configuration State) :
    RandomFunctionMACNativeCaller.Native.observe (relocate frame) = RandomFunctionMACNativeCaller.Native.observe frame := by
  cases frame with
  | mk state control trace => cases control <;> rfl

def EncodedPair (entry : List Bool × List Bool) : Prop :=
  ∃ message : Message, ∃ tag : Tag, entry = (encodeMessage message, encodeTag tag)

theorem extend_encoded (message : Message) (tag : Tag) (trace : List (List Bool × List Bool))
    (valid : ∀ entry ∈ trace, EncodedPair entry) :
    ∀ entry ∈ RandomFunctionMACNativeCaller.Native.extendTrace message tag trace, EncodedPair entry := by
  intro entry member
  rcases List.mem_cons.mp member with same | old
  · subst entry; exact ⟨message, tag, rfl⟩
  · exact valid entry old

theorem execution_encoded {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (valid : ∀ entry ∈ trace, EncodedPair entry)
    (coin : Bool) (final : Configuration State) (supported : final ∈ (executionLaw world state trace coin).support) :
    ∀ entry ∈ final.reverseTrace, EncodedPair entry := by
  rw [executionLaw, PMF.mem_support_bind_iff] at supported
  obtain ⟨first, _, supported⟩ := supported
  rw [PMF.mem_support_bind_iff] at supported
  obtain ⟨second, _, supported⟩ := supported
  rw [PMF.mem_support_bind_iff] at supported
  obtain ⟨repeated, _, supported⟩ := supported
  rw [PMF.mem_support_map_iff] at supported
  obtain ⟨actual, _, rfl⟩ := supported
  exact extend_encoded 7 actual.2 _ (extend_encoded (firstMessage coin) repeated.2 _
    (extend_encoded (secondMessage first.2) second.2 _ (extend_encoded (firstMessage coin) first.2 trace valid)))

theorem prefix_encoded {State : Type} (world : Oracle Message Tag State) (state : State)
    (fuel : Nat) (within : fuel ≤ 286) (current : Configuration State)
    (supported : current ∈ (TimedExecution.eval (Reification.timedStep code (packetOracle world)) fuel
      (⟨state, .running {}, []⟩ : Configuration State)).support) :
    ∀ entry ∈ current.reverseTrace, EncodedPair entry := by
  obtain ⟨final, finalSupported, included⟩ := Reification.extend_prefix code (packetOracle world) fuel 286 within
    ⟨state, .running {}, []⟩ current supported
  rw [whole_run, PMF.mem_support_bind_iff] at finalSupported
  obtain ⟨coin, _, finalSupported⟩ := finalSupported
  intro entry member
  exact execution_encoded world state [] (by intro entry member; cases member) coin final finalSupported entry (included member)

theorem awaiting_format {State : Type} (world : Oracle Message Tag State) (state : State)
    (fuel : Nat) (within : fuel ≤ 286) (current : Configuration State)
    (supported : current ∈ (TimedExecution.eval (Reification.timedStep code (packetOracle world)) fuel
      (⟨state, .running {}, []⟩ : Configuration State)).support)
    (machine : Machine.Configuration) (request : List Bool) (waiting : current.control = .awaiting machine request) :
    ∃ message : Message, request = encodeMessage message := by
  have before : fuel < 286 := by
    by_contra notBefore
    have last : fuel = 286 := by omega
    subst fuel
    have halted := (whole_halts_queries world state [] current supported).1
    simp [waiting, Reification.terminal] at halted
  obtain ⟨answer, reachable⟩ := PMF.support_nonempty (packetOracle world current.state request)
  let next : Configuration State := ⟨answer.1, .loading machine answer.2 {}, (request, answer.2) :: current.reverseTrace⟩
  have stepLaw : Reification.timedStep code (packetOracle world) current =
      (packetOracle world current.state request).map (fun response =>
        (⟨response.1, .loading machine response.2 {}, (request, response.2) :: current.reverseTrace⟩ : Configuration State)) := by
    simp [Reification.timedStep, waiting, Reification.terminal, Reification.perform, Reification.action, transition]
  have stepSupported : next ∈ (Reification.timedStep code (packetOracle world) current).support := by
    rw [stepLaw, PMF.mem_support_map_iff]
    exact ⟨answer, reachable, rfl⟩
  have nextSupported : next ∈ (TimedExecution.eval (Reification.timedStep code (packetOracle world)) (fuel + 1)
      (⟨state, .running {}, []⟩ : Configuration State)).support := by
    rw [TimedExecution.eval_add, PMF.mem_support_bind_iff]
    refine ⟨current, supported, ?_⟩
    simpa [TimedExecution.eval] using stepSupported
  obtain ⟨message, _tag, equal⟩ := prefix_encoded world state (fuel + 1) (by omega) next nextSupported
    (request, answer.2) (List.mem_cons_self ..)
  exact ⟨message, congrArg Prod.fst equal⟩

end Foundation.Symmetric.RandomFunctionMACNativeOptimized
