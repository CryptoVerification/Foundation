import Foundation.Crypto.Semantics.Oracle.FixedWidthCopy

/-! Fixed-width runtime reversal: read output cells leftwards while writing
input cells rightwards. Explicitly reserved destination cells separate the
written region from a retained private table or other continuation data. -/
namespace CryptoOracle.Interactive.ReverseOutputCopy
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def cellCode (base fault : Nat) : Code :=
  [.native (.branch .output fault (base + 1) (base + 3)),
   .native (.write .input false), .native (.jump (base + 5)),
   .native (.write .input true), .native (.jump (base + 5)),
   .native (.moveLeft .output), .native (.moveRight .input)]

def code (base : Nat) : Nat → Nat → Code
  | 0, _ => []
  | width + 1, fault => cellCode base fault ++ code (base + 7) width fault

theorem cellCode_length (base fault : Nat) : (cellCode base fault).length = 7 := rfl

theorem code_length (base width fault : Nat) : (code base width fault).length = 7 * width := by
  induction width generalizing base with
  | zero => rfl
  | succ width ih => simp [code, cellCode_length, ih]; omega

theorem code_native (base width fault : Nat) :
    ∀ i ∈ code base width fault, ∃ op, i = .native op := by
  induction width generalizing base with
  | zero => simp [code]
  | succ width ih =>
      intro i hi
      simp only [code, List.mem_append] at hi
      rcases hi with hi | hi
      · simp only [cellCode, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
      · exact ih _ i hi

theorem cell_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (before after : Code) (fault : Nat)
    (machine : Machine.Configuration) (bit : Bool)
    (pc : machine.pc = before.length) (active : machine.halted = false)
    (current : machine.outputTape.current = some bit) :
    TimedExecution.eval (Reification.timedStep (before ++ cellCode before.length fault ++ after) oracle) 5
      (⟨state, .running machine, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := before.length + 7, inputTape := (machine.inputTape.write (some bit)).moveRight, outputTape := machine.outputTape.moveLeft }, trace⟩ := by
  cases bit <;>
    simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition, cellCode, pc, active, current,
      Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
      Machine.Configuration.advance, List.getElem?_append, Nat.add_assoc]

theorem destination_move (left cells : List (Option Bool)) (bit : Bool) :
    ((FixedWidthCopy.frontier left (none :: cells)).write (some bit)).moveRight =
      FixedWidthCopy.frontier (some bit :: left) cells := by
  cases cells <;> rfl

/-- Both source surroundings and the complete destination tail are retained.
The blank corridor is an entry obligation, not an uncharged allocation step. -/
theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (before after : Code) (fault : Nat)
    (targetLeft targetTail sourceRight sourceLeft : List (Option Bool)) (bits : List Bool) :
    TimedExecution.eval (Reification.timedStep (before ++ code before.length bits.length fault ++ after) oracle)
      (5 * bits.length)
      (⟨state, .running { pc := before.length, inputTape := FixedWidthCopy.frontier targetLeft (List.replicate bits.length none ++ targetTail), outputTape := FixedWidthCopy.backwardFrontier sourceRight (bits.map some ++ sourceLeft) }, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running { pc := before.length + 7 * bits.length, inputTape := FixedWidthCopy.frontier (bits.reverse.map some ++ targetLeft) targetTail, outputTape := FixedWidthCopy.backwardFrontier (bits.reverse.map some ++ sourceRight) sourceLeft }, trace⟩ := by
  induction bits generalizing before targetLeft sourceRight with
  | nil => simp [code, TimedExecution.eval]
  | cons bit rest ih =>
      rw [show 5 * (bit :: rest).length = 5 + 5 * rest.length from by simp; omega,
        TimedExecution.eval_add]
      have hc := cell_run oracle state trace before
        (code (before.length + 7) rest.length fault ++ after) fault
        { pc := before.length, inputTape := FixedWidthCopy.frontier targetLeft (List.replicate (bit :: rest).length none ++ targetTail), outputTape := FixedWidthCopy.backwardFrontier sourceRight ((bit :: rest).map some ++ sourceLeft) }
        bit rfl rfl rfl
      simp only [List.length_cons, code, List.append_assoc] at ⊢
      simp only [List.append_assoc, List.length_cons] at hc
      rw [hc, PMF.pure_bind]
      simp only [List.map_cons, List.cons_append, List.replicate_succ, destination_move,
        FixedWidthCopy.backwardFrontier_move]
      have hrest := ih (before ++ cellCode before.length fault)
        (some bit :: targetLeft) (some bit :: sourceRight)
      simp only [List.length_append, cellCode_length, List.append_assoc] at hrest
      rw [hrest]
      simp [List.reverse_cons, List.map_append, List.append_assoc, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm]

end CryptoOracle.Interactive.ReverseOutputCopy
