import Foundation.Constructions.Hash.NativeRuntimeExecution

/-! End-to-end native hashing with a runtime message. For fixed public hash
parameters, exactly the same finite code accepts every valid finite message.
Only the execution budget depends on the number of message blocks. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false

def runtimeHashCode (initial terminal : List Bool) : Code :=
  StraightLine.code (initializeActions initial) ++
    runtimeLoopCode (3 * initial.length) initial.length terminal

def runtimeHashSteps (n κ count : Nat) : Nat := 3 * n + runtimeLoopSteps n κ count

def runtimeFinalInput (message : List (List Bool)) : Tape :=
  FixedWidthCopy.frontier ((runtimePayloadBits message).reverse.map some) [some true]

theorem runtimeInput_tape (bits : List Bool) :
    FixedWidthCopy.frontier [] (bits.map some) = Tape.ofBits bits := by
  cases bits <;> rfl

/-- Initialization and the common loop realize the original adaptive iteration
from blank output. The input message is neither embedded in code nor rebuilt
by a host-language callback during execution. -/
theorem runtime_initialized_framed_run {State : Type*} (oracle : BitOracle State)
    (initial terminal : List Bool) (message : List (List Bool)) (state : State)
    (width : ∀ state request answer, answer ∈ (oracle state request).support →
      answer.2.length = initial.length)
    (messageWidth : ∀ payload ∈ message, payload.length = terminal.length) (beforeInput tail : List (Option Bool)) :
    Reification.eval (runtimeHashCode initial terminal) oracle
      (runtimeHashSteps initial.length terminal.length message.length)
      (⟨state, .running { inputTape := FixedWidthCopy.frontier beforeInput ((runtimeInputBits message).map some ++ tail) }, []⟩ : Configuration State) =
    ((Foundation.Hash.iterate initial (markedBlocks terminal message)).run
      (Program.adaptOracle (fun pair => pair.1 ++ pair.2) id oracle) state).map
      (iterationFinish (runtimeHaltPc (3 * initial.length) initial.length terminal.length)
        (FixedWidthCopy.frontier ((runtimePayloadBits message).reverse.map some ++ beforeInput) (some true :: tail)) []) := by
  rw [← Reification.timed_eval_eq, runtimeHashSteps, TimedExecution.eval_add]
  have init := StraightLine.public_run oracle state [] []
    (runtimeLoopCode (3 * initial.length) initial.length terminal)
    (initializeActions initial) { inputTape := FixedWidthCopy.frontier beforeInput ((runtimeInputBits message).map some ++ tail) } rfl rfl
  rw [initializeActions_length] at init
  change TimedExecution.eval _ _
    (⟨state, .running { pc := 0, inputTape := FixedWidthCopy.frontier beforeInput ((runtimeInputBits message).map some ++ tail) }, []⟩ : Configuration State) = _ at init
  rw [initialize_execute] at init
  simp only [List.nil_append, Nat.zero_add] at init
  change (TimedExecution.eval (Reification.timedStep (runtimeHashCode initial terminal) oracle)
    (3 * initial.length) _).bind _ = _
  simp only [runtimeHashCode]
  rw [init, PMF.pure_bind]
  have loopRun := runtime_loop_run oracle initial.length width
    (StraightLine.code (initializeActions initial)) [] terminal state [] beforeInput initial message rfl messageWidth tail
  simpa only [List.append_nil, List.length_append, StraightLine.code, List.length_map,
    initializeActions_length, runtimeInput_tape, Nat.zero_add, List.append_nil,
    runtimeFinalInput] using loopRun

-- The original empty-frame contract is preserved as a specialization.
theorem runtime_initialized_run {State : Type*} (oracle : BitOracle State)
    (initial terminal : List Bool) (message : List (List Bool)) (state : State)
    (width : ∀ state request answer, answer ∈ (oracle state request).support →
      answer.2.length = initial.length)
    (messageWidth : ∀ payload ∈ message, payload.length = terminal.length) :
    Reification.eval (runtimeHashCode initial terminal) oracle
      (runtimeHashSteps initial.length terminal.length message.length)
      (Configuration.initial state (runtimeInputBits message)) =
    ((Foundation.Hash.iterate initial (markedBlocks terminal message)).run
      (Program.adaptOracle (fun pair => pair.1 ++ pair.2) id oracle) state).map
      (iterationFinish (runtimeHaltPc (3 * initial.length) initial.length terminal.length)
        (runtimeFinalInput message) []) := by
  simpa only [List.append_nil, runtimeInput_tape, runtimeFinalInput,
    Interactive.Configuration.initial, Machine.Configuration.initial] using
    runtime_initialized_framed_run oracle initial terminal message state width messageWidth [] []

/-- Exact realization of the prefix-free MD program by one finite runtime-input
hash code. The terminal payload and initial digest are public code parameters. -/
theorem runtime_prefixFree_framed_run {State : Type*} (oracle : BitOracle State)
    (initial terminal : List Bool) (message : List (List Bool)) (state : State)
    (width : ∀ state request answer, answer ∈ (oracle state request).support →
      answer.2.length = initial.length)
    (messageWidth : ∀ payload ∈ message, payload.length = terminal.length) (beforeInput tail : List (Option Bool)) :
    Reification.eval (runtimeHashCode initial terminal) oracle
      (runtimeHashSteps initial.length terminal.length message.length)
      (⟨state, .running { inputTape := FixedWidthCopy.frontier beforeInput ((runtimeInputBits message).map some ++ tail) }, []⟩ : Configuration State) =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run
      (Program.adaptOracle (fun pair => pair.1 ++ pair.2.1 :: pair.2.2) id oracle) state).map
      (hashFinish (runtimeHaltPc (3 * initial.length) initial.length terminal.length)
        (FixedWidthCopy.frontier ((runtimePayloadBits message).reverse.map some ++ beforeInput) (some true :: tail))) := by
  rw [runtime_initialized_framed_run oracle initial terminal message state width messageWidth beforeInput tail,
    markedBlocks, iterate_encoded_run]
  have adapters :
      Program.adaptOracle (fun pair : List Bool × (Bool × List Bool) => (pair.1, pair.2.1 :: pair.2.2)) id
        (Program.adaptOracle (fun pair : List Bool × List Bool => pair.1 ++ pair.2) id oracle) =
      Program.adaptOracle (fun pair => pair.1 ++ pair.2.1 :: pair.2.2) id oracle := by
    funext s request
    simp [Program.adaptOracle, PMF.map_comp, Function.comp_def]
  rw [adapters]
  simp only [PMF.map_comp, Function.comp_def, Foundation.Hash.prefixFreeMD]
  congr 1
  funext out
  simp [hashFinish, iterationFinish, Program.mapTranscript, encodeIterationTrace,
    List.map_map, Function.comp_def]

-- Preserve the original empty-frame hash contract.
theorem runtime_prefixFree_run {State : Type*} (oracle : BitOracle State)
    (initial terminal : List Bool) (message : List (List Bool)) (state : State)
    (width : ∀ state request answer, answer ∈ (oracle state request).support →
      answer.2.length = initial.length)
    (messageWidth : ∀ payload ∈ message, payload.length = terminal.length) :
    Reification.eval (runtimeHashCode initial terminal) oracle
      (runtimeHashSteps initial.length terminal.length message.length)
      (Configuration.initial state (runtimeInputBits message)) =
    ((Foundation.Hash.prefixFreeMD initial terminal message).run
      (Program.adaptOracle (fun pair => pair.1 ++ pair.2.1 :: pair.2.2) id oracle) state).map
      (hashFinish (runtimeHaltPc (3 * initial.length) initial.length terminal.length)
        (runtimeFinalInput message)) := by
  simpa only [List.append_nil, runtimeInput_tape, runtimeFinalInput,
    Interactive.Configuration.initial, Machine.Configuration.initial] using
    runtime_prefixFree_framed_run oracle initial terminal message state width messageWidth [] []

/-- Every supported execution halts; reaching the evaluator budget alone is
not treated as completion. Oracle internal running time remains external. -/
theorem runtime_prefixFree_halts {State : Type*} (oracle : BitOracle State)
    (initial terminal : List Bool) (message : List (List Bool)) (state : State)
    (width : ∀ state request answer, answer ∈ (oracle state request).support →
      answer.2.length = initial.length)
    (messageWidth : ∀ payload ∈ message, payload.length = terminal.length) :
    Reification.HaltsWithin (runtimeHashCode initial terminal) oracle
      (Configuration.initial state (runtimeInputBits message))
      (runtimeHashSteps initial.length terminal.length message.length) := by
  intro finish hFinish
  rw [runtime_prefixFree_run oracle initial terminal message state width messageWidth,
    PMF.mem_support_map_iff] at hFinish
  obtain ⟨out, _, rfl⟩ := hFinish
  rfl

/-- The finite instruction count is independent of message length. -/
theorem runtimeHashCode_length (initial terminal : List Bool) :
    (runtimeHashCode initial terminal).length = 7 * initial.length + 11 * terminal.length + 13 := by
  simp [runtimeHashCode, StraightLine.code]
  omega

/-- A native transition budget, not wall-clock time or an exact first-arrival
claim. All explicit copying, transfer, initialization and branching is counted. -/
theorem runtimeHashSteps_formula (n κ count : Nat) :
    runtimeHashSteps n κ count =
      3 * n + count * (7 * n + 8 * κ + 14) + (7 * n + 5 * κ + 13) := by
  simp [runtimeHashSteps, runtimeLoopSteps, Nat.add_assoc]

end Foundation.Hash.Native
