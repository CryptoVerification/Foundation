import Foundation.Crypto.Semantics.Oracle.FixedWidthCopy

/-! Additional finite-copy primitives for the simulator's terminal
recognition: a forward copy reading the output tape, a fixed-width
cross-tape equality test, and a reversal copy whose heads move in
opposite directions. All reuse the existing seven-instruction cell code
and the existing transition semantics. -/
namespace CryptoOracle.Interactive.TerminalCopy
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {State : Type*}

/-- One rightward copy cell reading the output tape and writing the input
tape. The existing cell code is shared; only the tape roles differ. -/
theorem readOutput_cell_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (before after : Code) (fault : Nat)
    (machine : Machine.Configuration) (bit : Bool)
    (pc : machine.pc = before.length) (active : machine.halted = false)
    (input : machine.outputTape.current = some bit) :
    TimedExecution.eval (Reification.timedStep
      (before ++ FixedWidthCopy.cellCodeWith true false before.length fault ++ after) oracle) 5
      (⟨state, .running machine, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := before.length + 7, inputTape := (machine.inputTape.write (some bit)).moveRight, outputTape := machine.outputTape.moveRight }, trace⟩ := by
  cases bit <;>
    simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition, FixedWidthCopy.cellCodeWith, pc, active, input,
      Machine.Instruction.next, Configuration.tape, Configuration.updateTape,
      Configuration.advance, Tape.write, Tape.moveRight, List.getElem?_append, Nat.add_assoc]

/-- The full rightward copy reading the output tape into the input tape,
cell for cell. The roles are exactly those of the existing forward copy. -/
theorem readOutput_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (before after : Code) (fault : Nat)
    (beforeInput beforeOutput tail : List (Option Bool)) (bits : List Bool) :
    TimedExecution.eval (Reification.timedStep
      (before ++ FixedWidthCopy.codeWith true false before.length bits.length fault ++ after) oracle)
      (5 * bits.length)
      (⟨state, .running { pc := before.length, inputTape := { left := beforeInput }, outputTape := FixedWidthCopy.frontier beforeOutput (bits.map some ++ tail) }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := before.length + 7 * bits.length, inputTape := { left := bits.reverse.map some ++ beforeInput }, outputTape := FixedWidthCopy.frontier (bits.reverse.map some ++ beforeOutput) tail }, trace⟩ := by
  induction bits generalizing before beforeInput beforeOutput with
  | nil => simp [FixedWidthCopy.codeWith, TimedExecution.eval]
  | cons bit bits ih =>
      rw [show 5 * (bit :: bits).length = 5 + 5 * bits.length by simp; omega, TimedExecution.eval_add]
      have hc := readOutput_cell_run oracle state trace before
        (FixedWidthCopy.codeWith true false (before.length + 7) bits.length fault ++ after) fault
        { pc := before.length, inputTape := { left := beforeInput }, outputTape := FixedWidthCopy.frontier beforeOutput ((bit :: bits).map some ++ tail) } bit rfl rfl rfl
      simp only [List.length_cons, FixedWidthCopy.codeWith, List.append_assoc] at ⊢
      simp only [List.append_assoc] at hc
      rw [hc, PMF.pure_bind]
      simp only [List.map_cons, List.cons_append, FixedWidthCopy.frontier_move, Tape.write]
      simp only [Tape.moveRight, List.append_assoc]
      have rest := ih (before ++ FixedWidthCopy.cellCodeWith true false before.length fault)
        (some bit :: beforeInput) (some bit :: beforeOutput)
      simp only [List.length_append, FixedWidthCopy.cellCodeWith_length, List.append_assoc] at rest
      rw [rest]
      simp [List.reverse_cons, List.map_append, List.append_assoc, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm]

/-- The same leftward test stated for a closed code: the code itself starts
at `base`, so iterations never carry an address-carrying prefix. -/
def cellLeft (base fault : Nat) (b : Bool) : Code :=
  [.native (.branch .output fault (if b then fault else base + 1) (if b then base + 1 else fault)),
   .native (.moveLeft .output)]

/-- The two-instruction length of the leftward fixed-bit test. -/
theorem cellLeft_length (base fault : Nat) (b : Bool) : (cellLeft base fault b).length = 2 := rfl

theorem cellLeft_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (before after : Code) (fault : Nat) (b : Bool)
    (machine : Machine.Configuration)
    (pc : machine.pc = before.length) (active : machine.halted = false)
    (current : machine.outputTape.current = some b) :
    TimedExecution.eval (Reification.timedStep (before ++ cellLeft before.length fault b ++ after) oracle) 2
      (⟨state, .running machine, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := before.length + 2, inputTape := machine.inputTape, outputTape := machine.outputTape.moveLeft }, trace⟩ := by
  cases b <;>
    simp [cellLeft, TimedExecution.eval, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition, pc, active, current,
      Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
      Machine.Configuration.advance, List.getElem?_append, Nat.add_assoc, Tape.write, Tape.moveLeft]

/-- One fixed-bit equality test of two tape cells, moving right on both
tapes. A mismatch or a blank cell branches to the explicit fault address. -/
def cellBoth (base fault mismatch : Nat) : Code :=
  [.native (.branch .input fault (base + 1) (base + 6)),
   .native (.branch .output fault (base + 2) (base + 5)),
   .native (.moveRight .input),
   .native (.moveRight .output),
   .native (.jump (base + 7)),
   .native (.jump mismatch),
   .native (.branch .output fault (base + 5) (base + 2))]

theorem cellBoth_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (before after : Code) (fault mismatch : Nat)
    (machine : Machine.Configuration) (inputBit outputBit : Bool)
    (pc : machine.pc = before.length) (active : machine.halted = false)
    (hInput : machine.inputTape.current = some inputBit)
    (hOutput : machine.outputTape.current = some outputBit)
    (hEq : inputBit = outputBit) :
    TimedExecution.eval (Reification.timedStep (before ++ cellBoth before.length fault mismatch ++ after) oracle) 5
      (⟨state, .running machine, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := before.length + 7, inputTape := machine.inputTape.moveRight, outputTape := machine.outputTape.moveRight }, trace⟩ := by
  subst hEq
  cases inputBit <;>
    simp [cellBoth, TimedExecution.eval, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition, pc, active, hInput, hOutput,
      Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
      Machine.Configuration.advance, List.getElem?_append, Nat.add_assoc, Tape.write,
      Tape.moveRight]

end CryptoOracle.Interactive.TerminalCopy
