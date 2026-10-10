import Foundation.Constructions.Hash.NativeRuntimeBlock
import Foundation.Constructions.Hash.NativeHash

/-! A finite input-driven hash loop. The program counter returns to one fixed
branch after each data block. Code and addresses depend on digest/payload
widths and the public terminal payload, not on message values or length. -/
namespace Foundation.Hash.Native
open CryptoOracle CryptoOracle.Interactive Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false

def runtimeJumpPc (base n κ : Nat) : Nat := base + 1 + (2 * n + 8 * κ + 5)
def runtimeTerminalPc (base n κ : Nat) : Nat := runtimeJumpPc base n κ + 1
def runtimeHaltPc (base n κ : Nat) : Nat := runtimeTerminalPc base n κ + (2 * n + 3 * (κ + 1) + 1)
def runtimeFaultPc (base n κ : Nat) : Nat := runtimeHaltPc base n κ + 1

def runtimeBranch (base n κ : Nat) : Interactive.Instruction :=
  Interactive.Instruction.native (.branch .input (runtimeFaultPc base n κ) (base + 1) (runtimeTerminalPc base n κ))

def runtimeLoopCode (base n : Nat) (terminal : List Bool) : Code :=
  [runtimeBranch base n terminal.length] ++
    runtimeDataCode (base + 1) n terminal.length (runtimeFaultPc base n terminal.length) ++
    [Interactive.Instruction.native (.jump base)] ++ compressionCode n (true :: terminal) ++
    [Interactive.Instruction.native .halt, Interactive.Instruction.native .halt]

@[simp] theorem runtimeLoopCode_length (base n : Nat) (terminal : List Bool) :
    (runtimeLoopCode base n terminal).length = 4 * n + 11 * terminal.length + 13 := by
  simp [runtimeLoopCode]
  omega

/-- One deterministic native instruction in the existing public controller. -/
theorem runtime_native_one {State : Type*} (host : Code) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool))
    (machine next : Machine.Configuration) (instruction : Machine.Instruction)
    (active : machine.halted = false)
    (lookup : host[machine.pc]? = some (Interactive.Instruction.native instruction))
    (transition_eq : instruction.next machine = .inl next) :
    TimedExecution.eval (Reification.timedStep host oracle) 1
      (⟨state, .running machine, trace⟩ : Configuration State) =
    PMF.pure ⟨state, .running next, trace⟩ := by
  simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
    Reification.perform, Reification.action, transition, active, lookup, transition_eq]

theorem runtime_branch_lookup (before after : Code) (n : Nat) (terminal : List Bool) :
    (before ++ runtimeLoopCode before.length n terminal ++ after)[before.length]? =
      some (runtimeBranch before.length n terminal.length) := by
  simp [runtimeLoopCode, List.append_assoc]

theorem runtime_jump_lookup (before after : Code) (n : Nat) (terminal : List Bool) :
    (before ++ runtimeLoopCode before.length n terminal ++ after)[runtimeJumpPc before.length n terminal.length]? =
      some (Interactive.Instruction.native (.jump before.length)) := by
  have pos : runtimeJumpPc before.length n terminal.length =
      (before ++ [runtimeBranch before.length n terminal.length] ++
        runtimeDataCode (before.length + 1) n terminal.length (runtimeFaultPc before.length n terminal.length)).length := by
    simp [runtimeJumpPc]
    omega
  rw [pos]
  simpa only [runtimeLoopCode, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
    (show ((before ++ [runtimeBranch before.length n terminal.length] ++
        runtimeDataCode (before.length + 1) n terminal.length (runtimeFaultPc before.length n terminal.length)) ++
      Interactive.Instruction.native (.jump before.length) :: (compressionCode n (true :: terminal) ++ [Interactive.Instruction.native .halt, Interactive.Instruction.native .halt] ++ after))[(before ++ [runtimeBranch before.length n terminal.length] ++
        runtimeDataCode (before.length + 1) n terminal.length (runtimeFaultPc before.length n terminal.length)).length]? =
      some (Interactive.Instruction.native (.jump before.length)) by simp)

theorem runtime_halt_lookup (before after : Code) (n : Nat) (terminal : List Bool) :
    (before ++ runtimeLoopCode before.length n terminal ++ after)[runtimeHaltPc before.length n terminal.length]? =
      some (Interactive.Instruction.native .halt) := by
  have pos : runtimeHaltPc before.length n terminal.length =
      (before ++ [runtimeBranch before.length n terminal.length] ++
        runtimeDataCode (before.length + 1) n terminal.length (runtimeFaultPc before.length n terminal.length) ++
        [Interactive.Instruction.native (.jump before.length)] ++ compressionCode n (true :: terminal)).length := by
    simp [runtimeHaltPc, runtimeTerminalPc, runtimeJumpPc]
    omega
  rw [pos]
  simpa only [runtimeLoopCode, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
    (show ((before ++ [runtimeBranch before.length n terminal.length] ++
        runtimeDataCode (before.length + 1) n terminal.length (runtimeFaultPc before.length n terminal.length) ++
        [Interactive.Instruction.native (.jump before.length)] ++ compressionCode n (true :: terminal)) ++
      Interactive.Instruction.native .halt :: Interactive.Instruction.native .halt :: after)[(before ++ [runtimeBranch before.length n terminal.length] ++
        runtimeDataCode (before.length + 1) n terminal.length (runtimeFaultPc before.length n terminal.length) ++
        [Interactive.Instruction.native (.jump before.length)] ++ compressionCode n (true :: terminal)).length]? =
      some (Interactive.Instruction.native .halt) by simp)

/-- One loop round consumes one data block and returns to the same branch.
All oracle responses are processed by the same finite code. -/
theorem runtime_loop_data {State : Type*} (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (before after : Code)
    (beforeInput tail : List (Option Bool)) (digest payload terminal : List Bool)
    (payloadWidth : payload.length = terminal.length)
    (width : ∀ answer ∈ (oracle state (digest ++ false :: payload)).support,
      answer.2.length = digest.length) :
    TimedExecution.eval
      (Reification.timedStep (before ++ runtimeLoopCode before.length digest.length terminal ++ after) oracle)
      (7 * digest.length + 8 * terminal.length + 14)
      (⟨state, .running { pc := before.length, inputTape := FixedWidthCopy.frontier beforeInput (some false :: (payload.map some ++ tail)), outputTape := ResponseLoading.loaded digest }, trace⟩ : Configuration State) =
    (oracle state (digest ++ false :: payload)).map (fun answer =>
      (⟨answer.1, .running { pc := before.length, inputTape := FixedWidthCopy.frontier ((false :: payload).reverse.map some ++ beforeInput) tail, outputTape := ResponseLoading.loaded answer.2 },
        (digest ++ false :: payload, answer.2) :: trace⟩ : Configuration State)) := by
  rw [show 7 * digest.length + 8 * terminal.length + 14 =
      1 + ((7 * digest.length + 8 * payload.length + 12) + 1) by omega,
    TimedExecution.eval_add]
  have branchRun := runtime_native_one
    (before ++ runtimeLoopCode before.length digest.length terminal ++ after) oracle state trace
    { pc := before.length, inputTape := FixedWidthCopy.frontier beforeInput (some false :: (payload.map some ++ tail)), outputTape := ResponseLoading.loaded digest }
    { pc := before.length + 1, inputTape := FixedWidthCopy.frontier beforeInput (some false :: (payload.map some ++ tail)), outputTape := ResponseLoading.loaded digest }
    (.branch .input (runtimeFaultPc before.length digest.length terminal.length) (before.length + 1) (runtimeTerminalPc before.length digest.length terminal.length))
    rfl (runtime_branch_lookup before after digest.length terminal)
    (by rfl)
  rw [branchRun, PMF.pure_bind, TimedExecution.eval_add]
  have dataRun := runtime_data_run oracle state trace
    (before ++ [runtimeBranch before.length digest.length terminal.length])
    ([Interactive.Instruction.native (.jump before.length)] ++ compressionCode digest.length (true :: terminal) ++ [Interactive.Instruction.native .halt, Interactive.Instruction.native .halt] ++ after)
    (runtimeFaultPc before.length digest.length terminal.length) beforeInput tail digest payload width
  simp only [List.length_append, List.length_singleton, payloadWidth, List.append_assoc] at dataRun
  simp only [runtimeLoopCode, List.append_assoc, payloadWidth] at ⊢
  rw [dataRun, PMF.bind_map]
  rw [← PMF.bindOnSupport_eq_bind]
  calc
    _ = (oracle state (digest ++ false :: payload)).bindOnSupport (fun answer _ => PMF.pure
      (⟨answer.1, .running { pc := before.length, inputTape := FixedWidthCopy.frontier ((false :: payload).reverse.map some ++ beforeInput) tail, outputTape := ResponseLoading.loaded answer.2 }, (digest ++ false :: payload, answer.2) :: trace⟩ : Configuration State)) := by
      congr 1
      funext answer _
      apply runtime_native_one _ oracle _ _ _ _ (.jump before.length) rfl
      · have h := runtime_jump_lookup before after digest.length terminal
        simpa [runtimeLoopCode, runtimeJumpPc, List.append_assoc, Nat.add_assoc] using h
      · rfl
    _ = _ := by rw [PMF.bindOnSupport_eq_bind]; rfl

/-- The terminal branch performs one final compression and genuinely halts. -/
theorem runtime_loop_terminal {State : Type*} (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (before after : Code)
    (beforeInput : List (Option Bool)) (digest terminal : List Bool)
    (width : ∀ answer ∈ (oracle state (digest ++ true :: terminal)).support,
      answer.2.length = digest.length) (tail : List (Option Bool) := []) :
    TimedExecution.eval
      (Reification.timedStep (before ++ runtimeLoopCode before.length digest.length terminal ++ after) oracle)
      (7 * digest.length + 5 * terminal.length + 13)
      (⟨state, .running { pc := before.length, inputTape := FixedWidthCopy.frontier beforeInput (some true :: tail), outputTape := ResponseLoading.loaded digest }, trace⟩ : Configuration State) =
    (oracle state (digest ++ true :: terminal)).map (fun answer =>
      (⟨answer.1, .running { pc := runtimeHaltPc before.length digest.length terminal.length, inputTape := FixedWidthCopy.frontier beforeInput (some true :: tail), outputTape := ResponseLoading.loaded answer.2, halted := true },
        (digest ++ true :: terminal, answer.2) :: trace⟩ : Configuration State)) := by
  rw [show 7 * digest.length + 5 * terminal.length + 13 =
      1 + ((7 * digest.length + 5 * (true :: terminal).length + 6) + 1) by simp; omega,
    TimedExecution.eval_add]
  have branchRun := runtime_native_one
    (before ++ runtimeLoopCode before.length digest.length terminal ++ after) oracle state trace
    { pc := before.length, inputTape := FixedWidthCopy.frontier beforeInput (some true :: tail), outputTape := ResponseLoading.loaded digest }
    { pc := runtimeTerminalPc before.length digest.length terminal.length, inputTape := FixedWidthCopy.frontier beforeInput (some true :: tail), outputTape := ResponseLoading.loaded digest }
    (.branch .input (runtimeFaultPc before.length digest.length terminal.length) (before.length + 1) (runtimeTerminalPc before.length digest.length terminal.length))
    rfl (runtime_branch_lookup before after digest.length terminal) (by rfl)
  rw [branchRun, PMF.pure_bind, TimedExecution.eval_add]
  have terminalRun := compression_run oracle state trace
    (before ++ [runtimeBranch before.length digest.length terminal.length] ++
      runtimeDataCode (before.length + 1) digest.length terminal.length (runtimeFaultPc before.length digest.length terminal.length) ++ [Interactive.Instruction.native (.jump before.length)])
    ([Interactive.Instruction.native .halt, Interactive.Instruction.native .halt] ++ after)
    (FixedWidthCopy.frontier beforeInput (some true :: tail)) digest (true :: terminal) width
  have pos : (before ++ [runtimeBranch before.length digest.length terminal.length] ++
      runtimeDataCode (before.length + 1) digest.length terminal.length (runtimeFaultPc before.length digest.length terminal.length) ++ [Interactive.Instruction.native (.jump before.length)]).length =
      runtimeTerminalPc before.length digest.length terminal.length := by
    simp [runtimeTerminalPc, runtimeJumpPc]
    omega
  rw [pos] at terminalRun
  simp only [List.append_assoc] at terminalRun
  simp only [runtimeLoopCode, List.append_assoc] at ⊢
  rw [terminalRun, PMF.bind_map]
  rw [← PMF.bindOnSupport_eq_bind]
  calc
    _ = (oracle state (digest ++ true :: terminal)).bindOnSupport (fun answer _ => PMF.pure
      (⟨answer.1, .running { pc := runtimeHaltPc before.length digest.length terminal.length, inputTape := FixedWidthCopy.frontier beforeInput (some true :: tail), outputTape := ResponseLoading.loaded answer.2, halted := true }, (digest ++ true :: terminal, answer.2) :: trace⟩ : Configuration State)) := by
      congr 1
      funext answer _
      apply runtime_native_one _ oracle _ _ _ _ .halt rfl
      · have h := runtime_halt_lookup before after digest.length terminal
        simpa [runtimeLoopCode, runtimeHaltPc, List.append_assoc, Nat.add_assoc] using h
      · simp [Machine.Instruction.next, runtimeHaltPc, Nat.add_assoc]
    _ = _ := by rw [PMF.bindOnSupport_eq_bind]; rfl

end Foundation.Hash.Native
