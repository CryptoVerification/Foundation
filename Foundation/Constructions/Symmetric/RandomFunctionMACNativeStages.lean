import Foundation.Constructions.Symmetric.RandomFunctionMACNativeExecution

/-! Continuing native MAC stages. The saved-memory representation is explicit:
cell zero contains the attacker's coin; cells one through eight contain the
saved tag when present. No stage resets the machine or its oracle state.
-/
namespace Foundation.Symmetric.RandomFunctionMACNativeCaller.Native
open Foundation.Probability CryptoOracle CryptoOracle.Interactive TimedExecution Machine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def memory (coin : Bool) : Option Tag → Tape
  | none => {current := some coin}
  | some saved => {current := some coin, right := (encodeTag saved).map some ++ [none]}

def machineAt (pc : Nat) (coin : Bool) (saved : Option Tag) (output : Tape) : Machine.Configuration :=
  {pc := pc, inputTape := memory coin saved, outputTape := output}

def returned (pc : Nat) (coin : Bool) (saved : Option Tag) (tag : Tag) : Machine.Configuration :=
  machineAt pc coin saved (ResponseLoading.loaded (encodeTag tag))

/-- Native request construction keeps all represented trailing response
cells after the explicit request delimiter. They are not silently erased. -/
def residue (tag : Tag) : List (Option Bool) := ((encodeTag tag).drop 4).map some ++ [none]

def secondCall (coin : Bool) (first : Tag) : Machine.Configuration :=
  machineAt 30 coin none (RequestExport.packetTape [] (residue first) (encodeMessage (secondMessage first)))

def thirdCall (coin : Bool) (second : Tag) : Machine.Configuration :=
  machineAt 119 coin (some second) (RequestExport.packetTape [] (residue second) (encodeMessage (firstMessage coin)))

def lastCall (coin : Bool) (candidate repeated : Tag) : Machine.Configuration :=
  machineAt 205 coin (some candidate) (RequestExport.packetTape [] (residue repeated) (encodeMessage 7))

/- Unfold just one execution step before simplifying its concrete state.
Unfolding `run` under every not-yet-applied continuation would instead expand
fetches at unknown counters and obscure the actual straight-line execution. -/
macro "mac_native_step" : tactic => `(tactic|
  (rw [NativeDeterministic.run]
   all_goals simp_all [NativeDeterministic.next?, code, dynamicPacket, saveTag, copyBits, copyBit, lastPacket,
     Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
     Machine.Configuration.advance, Tape.write, Tape.moveLeft, Tape.moveRight]))

theorem second_setup_checked (coin : Bool) (first : Tag) :
    NativeDeterministic.run code 12 (returned 16 coin none first) = some (secondCall coin first) := by
  by_cases even : first.val % 2 = 0
  · simp only [returned, machineAt, memory, secondCall,
      residue, ResponseLoading.loaded, ResponseLoading.fromCells, RequestExport.packetTape,
      encodeMessage, encodeTag, secondMessage, Machine.Binary.encode]
    repeat' mac_native_step
  · have odd : first.val % 2 = 1 := by omega
    simp only [returned, machineAt, memory, secondCall,
      residue, ResponseLoading.loaded, ResponseLoading.fromCells, RequestExport.packetTape,
      encodeMessage, encodeTag, secondMessage, Machine.Binary.encode]
    repeat' mac_native_step

theorem third_setup_checked (coin : Bool) (second : Tag) :
    NativeDeterministic.run code 12 (returned 105 coin (some second) second) =
      some (thirdCall coin second) := by
  cases coin <;>
    simp only [returned, machineAt, memory, thirdCall,
      residue, ResponseLoading.loaded, ResponseLoading.fromCells, RequestExport.packetTape,
      encodeMessage, encodeTag, firstMessage, Machine.Binary.encode] <;>
    repeat' mac_native_step

theorem last_setup_checked (coin : Bool) (candidate repeated : Tag) :
    NativeDeterministic.run code 10 (returned 195 coin (some candidate) repeated) =
      some (lastCall coin candidate repeated) := by
  simp only [returned, machineAt, memory, lastCall,
    residue, ResponseLoading.loaded, ResponseLoading.fromCells, RequestExport.packetTape,
    encodeMessage, encodeTag, Machine.Binary.encode]
  repeat' mac_native_step

def saveAddress (third : Bool) : Nat := if third then 121 else 31
def copyAddress (third : Bool) : Nat := if third then 122 else 32
def savedAddress (third : Bool) : Nat := if third then 195 else 105

theorem save_enter_checked (third coin : Bool) (saved : Option Tag) (tag : Tag) :
    NativeDeterministic.run code 1 (returned (saveAddress third) coin saved tag) =
      some (NativeCopyBlock.manyStart (copyAddress third) (memory coin saved).moveRight [] [] (encodeTag tag)) := by
  cases third <;>
    simp only [returned, machineAt, saveAddress, copyAddress, NativeCopyBlock.manyStart,
      ResponseLoading.loaded, ResponseLoading.fromCells, RequestExport.packetTape] <;>
    repeat' mac_native_step

/-- Rewind nine memory cells and eight response cells after the symbolic
copy. Old candidate bits are overwritten; no tape is reset at the handoff. -/
theorem save_rewind_checked (third coin : Bool) (saved : Option Tag) (tag : Tag) :
    NativeDeterministic.run code 17
      (NativeCopyBlock.manyFinish (copyAddress third) (memory coin saved).moveRight [] [] (encodeTag tag)) =
      some (returned (savedAddress third) coin (some tag) tag) := by
  cases third <;> cases saved <;>
    simp only [returned, machineAt, memory, copyAddress, savedAddress, NativeCopyBlock.manyFinish,
      NativeCopyBlock.written, encodeTag, Machine.Binary.encode, List.length_cons, List.length_nil,
      ResponseLoading.loaded, ResponseLoading.fromCells, RequestExport.packetTape] <;>
    repeat' mac_native_step

theorem save_tag_checked (third coin : Bool) (saved : Option Tag) (tag : Tag) :
    NativeDeterministic.run code 58 (returned (saveAddress third) coin saved tag) =
      some (returned (savedAddress third) coin (some tag) tag) := by
  have locations : ∀ index, index < (encodeTag tag).length →
      NativeCopyBlock.Located code (copyAddress third + 7 * index) 249 := by
    intro index inside
    exact copy_locations third ⟨index, by simpa only [tag_width] using inside⟩
  have copy := NativeCopyBlock.many_checked code (copyAddress third) 249
    (memory coin saved).moveRight [] [] (encodeTag tag) locations
  have copy40 : NativeDeterministic.run code 40
      (NativeCopyBlock.manyStart (copyAddress third) (memory coin saved).moveRight [] [] (encodeTag tag)) =
      some (NativeCopyBlock.manyFinish (copyAddress third) (memory coin saved).moveRight [] [] (encodeTag tag)) := by
    simpa only [tag_width, Nat.reduceMul] using copy
  rw [show 58 = 1 + (40 + 17) by rfl, NativeDeterministic.run_add, save_enter_checked,
    Option.bind_some, NativeDeterministic.run_add, copy40, Option.bind_some, save_rewind_checked]

theorem save_tag_run {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (third coin : Bool) (saved : Option Tag) (tag : Tag) :
    TimedExecution.eval (Reification.timedStep code oracle) 58
      (⟨state, .running (returned (saveAddress third) coin saved tag), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (returned (savedAddress third) coin (some tag) tag), trace⟩ :=
  NativeDeterministic.run_sound code oracle state trace 58 _ _ (save_tag_checked third coin saved tag)

theorem second_setup_run {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (first : Tag) :
    TimedExecution.eval (Reification.timedStep code oracle) 12
      (⟨state, .running (returned 16 coin none first), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (secondCall coin first), trace⟩ :=
  NativeDeterministic.run_sound code oracle state trace 12 _ _ (second_setup_checked coin first)

theorem third_setup_run {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (second : Tag) :
    TimedExecution.eval (Reification.timedStep code oracle) 12
      (⟨state, .running (returned 105 coin (some second) second), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (thirdCall coin second), trace⟩ :=
  NativeDeterministic.run_sound code oracle state trace 12 _ _ (third_setup_checked coin second)

theorem last_setup_run {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (candidate repeated : Tag) :
    TimedExecution.eval (Reification.timedStep code oracle) 10
      (⟨state, .running (returned 195 coin (some candidate) repeated), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (lastCall coin candidate repeated), trace⟩ :=
  NativeDeterministic.run_sound code oracle state trace 10 _ _ (last_setup_checked coin candidate repeated)

def extendTrace (message : Message) (tag : Tag) (trace : List (List Bool × List Bool)) :=
  (encodeMessage message, encodeTag tag) :: trace

theorem second_transfer {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (first : Tag) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 36
      (⟨state, .running (secondCall coin first), trace⟩ : Configuration State) =
      (world state (secondMessage first)).map (fun answer =>
        ⟨answer.1, .running (returned 31 coin none answer.2), extendTrace (secondMessage first) answer.2 trace⟩) := by
  have law := QueryTransfer.fixed_response_call code (packetOracle world) (secondCall coin first)
    state trace (encodeMessage (secondMessage first)) [] (residue first) rfl (by decide_cbv) rfl 8
    (packet_response_width world state (encodeMessage (secondMessage first)))
  simpa only [message_width, packetOracle, message_roundtrip, PMF.map_comp, Function.comp_def,
    QueryTransfer.resumed, Machine.Configuration.advance, secondCall, returned, machineAt, extendTrace] using law

theorem third_transfer {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (second : Tag) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 36
      (⟨state, .running (thirdCall coin second), trace⟩ : Configuration State) =
      (world state (firstMessage coin)).map (fun answer =>
        ⟨answer.1, .running (returned 120 coin (some second) answer.2), extendTrace (firstMessage coin) answer.2 trace⟩) := by
  have law := QueryTransfer.fixed_response_call code (packetOracle world) (thirdCall coin second)
    state trace (encodeMessage (firstMessage coin)) [] (residue second) rfl (by decide_cbv) rfl 8
    (packet_response_width world state (encodeMessage (firstMessage coin)))
  simpa only [message_width, packetOracle, message_roundtrip, PMF.map_comp, Function.comp_def,
    QueryTransfer.resumed, Machine.Configuration.advance, thirdCall, returned, machineAt, extendTrace] using law

theorem last_transfer {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (candidate repeated : Tag) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 36
      (⟨state, .running (lastCall coin candidate repeated), trace⟩ : Configuration State) =
      (world state 7).map (fun answer =>
        ⟨answer.1, .running (returned 206 coin (some candidate) answer.2), extendTrace 7 answer.2 trace⟩) := by
  have law := QueryTransfer.fixed_response_call code (packetOracle world) (lastCall coin candidate repeated)
    state trace (encodeMessage 7) [] (residue repeated) rfl (by decide_cbv) rfl 8
    (packet_response_width world state (encodeMessage 7))
  simpa only [message_width, packetOracle, message_roundtrip, PMF.map_comp, Function.comp_def,
    QueryTransfer.resumed, Machine.Configuration.advance, lastCall, returned, machineAt, extendTrace] using law

theorem second_query_run {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (first : Tag) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 48
      (⟨state, .running (returned 16 coin none first), trace⟩ : Configuration State) =
      (world state (secondMessage first)).map (fun answer =>
        ⟨answer.1, .running (returned 31 coin none answer.2), extendTrace (secondMessage first) answer.2 trace⟩) := by
  rw [show 48 = 12 + 36 by rfl, TimedExecution.eval_add, second_setup_run, PMF.pure_bind, second_transfer]

theorem third_query_run {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (second : Tag) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 48
      (⟨state, .running (returned 105 coin (some second) second), trace⟩ : Configuration State) =
      (world state (firstMessage coin)).map (fun answer =>
        ⟨answer.1, .running (returned 120 coin (some second) answer.2), extendTrace (firstMessage coin) answer.2 trace⟩) := by
  rw [show 48 = 12 + 36 by rfl, TimedExecution.eval_add, third_setup_run, PMF.pure_bind, third_transfer]

theorem last_query_run {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (candidate repeated : Tag) :
    TimedExecution.eval (Reification.timedStep code (packetOracle world)) 46
      (⟨state, .running (returned 195 coin (some candidate) repeated), trace⟩ : Configuration State) =
      (world state 7).map (fun answer =>
        ⟨answer.1, .running (returned 206 coin (some candidate) answer.2), extendTrace 7 answer.2 trace⟩) := by
  rw [show 46 = 10 + 36 by rfl, TimedExecution.eval_add, last_setup_run, PMF.pure_bind, last_transfer]

/-- The conditional save has a real, branch-dependent duration. In the false
branch its continuation starts immediately; it is not padded at this boundary. -/
theorem select_candidate_checked (coin : Bool) (second repeated : Tag) :
    NativeDeterministic.run code (if coin then 59 else 1) (returned 120 coin (some second) repeated) =
      some (returned 195 coin (some (if coin then repeated else second)) repeated) := by
  cases coin with
  | false =>
      simp only [Bool.false_eq_true, if_false, returned, machineAt, memory]
      repeat' mac_native_step
  | true =>
      change NativeDeterministic.run code (1 + 58) (returned 120 true (some second) repeated) = _
      rw [NativeDeterministic.run_add]
      have head : NativeDeterministic.run code 1 (returned 120 true (some second) repeated) =
          some (returned 121 true (some second) repeated) := by
        simp only [returned, machineAt, memory]
        repeat' mac_native_step
      rw [head, Option.bind_some]
      exact save_tag_checked true true (some second) repeated

theorem select_candidate_run {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (second repeated : Tag) :
    TimedExecution.eval (Reification.timedStep code oracle) (if coin then 59 else 1)
      (⟨state, .running (returned 120 coin (some second) repeated), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (returned 195 coin (some (if coin then repeated else second)) repeated), trace⟩ :=
  NativeDeterministic.run_sound code oracle state trace _ _ _ (select_candidate_checked coin second repeated)

end Foundation.Symmetric.RandomFunctionMACNativeCaller.Native
