import Foundation.Crypto.Semantics.Oracle.Refresh

/-! Syntactic comparisons of selected, genuinely stochastic state kernels.
An index chooses a coordinate from the fixed adaptive history, not from the
function currently being refreshed. Only adjacent exchange and contexts
generate Cell. Duplicate removal is a separate directed resource improvement.
There is no constructor accepting an arbitrary equality of kernels or laws.
One resource unit below means one tag draw, not one native CPU instruction.
-/
namespace CryptoOracle.ProofEdits.Refresh
open Foundation.Probability CryptoOracle.RandomOracle CryptoOracle.RandomOracle.Posterior
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

variable {Index Input Tag History : Type} [DecidableEq Input] [Fintype Tag] [Nonempty Tag]

inductive Cell : List Index → List Index → Type where
  | refl (word) : Cell word word
  | exchange (first second : Index) (tail : List Index) :
      Cell (first :: second :: tail) (second :: first :: tail)
  | cons (index) {first second} : Cell first second → Cell (index :: first) (index :: second)
  | symm {first second} : Cell first second → Cell second first
  | trans {first middle last} : Cell first middle → Cell middle last → Cell first last

theorem Cell.sound (coordinate : Index → History → Input) {first second : List Index}
    (cell : Cell first second) (state : History × (Input → Tag)) :
    run coordinate first state = run coordinate second state := by
  induction cell generalizing state with
  | refl => rfl
  | exchange first second tail =>
      change (step coordinate first state).bind (fun next =>
        (step coordinate second next).bind (run coordinate tail)) = _
      rw [← PMF.bind_bind, step_exchange]
      exact PMF.bind_bind _ _ _
  | cons index cell ih =>
      exact congrArg (PMF.bind (step coordinate index state)) (funext ih)
  | symm cell ih => exact (ih state).symm
  | trans left right ihLeft ihRight => exact (ihLeft state).trans (ihRight state)

theorem Cell.perm {first second : List Index} (cell : Cell first second) : first.Perm second := by
  induction cell with
  | refl word => exact List.Perm.refl word
  | exchange first second tail => exact List.Perm.swap ..
  | cons index cell ih => exact .cons index ih
  | symm cell ih => exact ih.symm
  | trans left right ihLeft ihRight => exact ihLeft.trans ihRight

theorem Cell.nonempty_of_perm {first second : List Index} (permutation : first.Perm second) :
    Nonempty (Cell first second) := by
  induction permutation with
  | nil => exact ⟨.refl []⟩
  | cons index permutation ih => obtain ⟨cell⟩ := ih; exact ⟨.cons index cell⟩
  | swap first second tail => exact ⟨.exchange _ _ _⟩
  | trans left right ihLeft ihRight =>
      obtain ⟨first⟩ := ihLeft
      obtain ⟨second⟩ := ihRight
      exact ⟨.trans first second⟩

theorem cell_iff_perm (first second : List Index) : Nonempty (Cell first second) ↔ first.Perm second :=
  ⟨fun ⟨cell⟩ => cell.perm, Cell.nonempty_of_perm⟩

theorem Cell.draws {first second : List Index} (cell : Cell first second) :
    first.length = second.length := cell.perm.length_eq

inductive Improvement : List Index → List Index → Type where
  | refl (word) : Improvement word word
  | exchange {first second} : Cell first second → Improvement first second
  | duplicate (index : Index) (tail : List Index) :
      Improvement (index :: index :: tail) (index :: tail)
  | cons (index) {first second} : Improvement first second →
      Improvement (index :: first) (index :: second)
  | trans {first middle last} : Improvement first middle → Improvement middle last → Improvement first last

theorem Improvement.sound (coordinate : Index → History → Input) {first second : List Index}
    (change : Improvement first second) (state : History × (Input → Tag)) :
    run coordinate first state = run coordinate second state := by
  induction change generalizing state with
  | refl => rfl
  | exchange cell => exact cell.sound coordinate state
  | duplicate index tail =>
      change (step coordinate index state).bind (fun next =>
        (step coordinate index next).bind (run coordinate tail)) = _
      rw [← PMF.bind_bind, step_duplicate]
      rfl
  | cons index change ih => exact congrArg (PMF.bind (step coordinate index state)) (funext ih)
  | trans first second ihFirst ihSecond => exact (ihFirst state).trans (ihSecond state)

theorem Improvement.draws {first second : List Index} (change : Improvement first second) :
    second.length ≤ first.length := by
  induction change with
  | refl => exact le_rfl
  | exchange cell => exact Nat.le_of_eq cell.draws.symm
  | duplicate => simp
  | cons index change ih => exact Nat.succ_le_succ ih
  | trans first second ihFirst ihSecond => exact ihSecond.trans ihFirst

variable [Fintype Input]

theorem Cell.joint_eq (history : PMF History) (table : History → Table Input Tag)
    (coordinate : Index → History → Input) {first second : List Index} (cell : Cell first second) :
    joint history table coordinate first = joint history table coordinate second := by
  unfold joint
  simp_rw [cell.sound coordinate]

omit [Fintype Input] in
theorem Cell.continuation {Result : Type} (coordinate : Index → History → Input)
    {first second : List Index} (cell : Cell first second)
    (next : (History × (Input → Tag)) → PMF Result) (state : History × (Input → Tag)) :
    (run coordinate first state).bind next = (run coordinate second state).bind next := by
  rw [cell.sound coordinate]

end CryptoOracle.ProofEdits.Refresh
