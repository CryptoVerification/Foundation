import Foundation.Crypto.Semantics.Oracle.InteractionRules

/-! Mixed local diagrams for lookup, recording and refresh on one shared
cache/function/trace state. Independence is syntactic. No rule exchanges
different queries or different history records, since their order is retained.
Neither whole-program equality nor arbitrary commuting kernels are inputs.
-/
namespace CryptoOracle.ProofEdits.Interaction
open Foundation.Probability CryptoOracle.RandomOracle
set_option backward.isDefEq.respectTransparency false
variable {Input Tag : Type} [DecidableEq Input]

variable [Fintype Tag] [Nonempty Tag]

inductive Cell : List (Action Input) → List (Action Input) → Type where
  | refl (word) : Cell word word
  | exchange (first second : Action Input) (allowed : independent first second = true) (tail) :
      Cell (first :: second :: tail) (second :: first :: tail)
  | cons (action) {first second} : Cell first second → Cell (action :: first) (action :: second)
  | symm {first second} : Cell first second → Cell second first
  | trans {first middle last} : Cell first middle → Cell middle last → Cell first last

theorem Cell.sound {first second : List (Action Input)} (cell : Cell first second) (state : State Input Tag) :
    run first state = run second state := by
  induction cell generalizing state with
  | refl => rfl
  | exchange first second allowed tail =>
      change (step first state).bind (fun next => (step second next).bind (run tail)) = _
      rw [← PMF.bind_bind, step_exchange first second allowed]
      exact PMF.bind_bind _ _ _
  | cons action cell ih => exact congrArg (PMF.bind (step action state)) (funext ih)
  | symm cell ih => exact (ih state).symm
  | trans first second ihFirst ihSecond => exact (ihFirst state).trans (ihSecond state)

omit [Fintype Tag] [Nonempty Tag] in
theorem Cell.scan {first second : List (Action Input)} (cell : Cell first second) (seen : Finset Input) :
    scan seen first = scan seen second := by
  induction cell generalizing seen with
  | refl => rfl
  | exchange first second allowed tail => exact scan_exchange seen first second tail allowed
  | cons action cell ih =>
      cases action with
      | query message => exact ih (insert message seen)
      | record message => exact ih seen
      | refresh message =>
          by_cases present : message ∈ seen <;> simp [Interaction.scan, present, ih seen]
  | symm cell ih => exact (ih seen).symm
  | trans first second ihFirst ihSecond => exact (ihFirst seen).trans (ihSecond seen)

omit [Fintype Tag] [Nonempty Tag] in
theorem Cell.perm {first second : List (Action Input)} (cell : Cell first second) : first.Perm second := by
  induction cell with
  | refl word => exact List.Perm.refl word
  | exchange first second allowed tail => exact List.Perm.swap ..
  | cons action cell ih => exact .cons action ih
  | symm cell ih => exact ih.symm
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

omit [Fintype Tag] [Nonempty Tag] in
theorem Cell.counts {first second : List (Action Input)} (cell : Cell first second) :
    queryCount first = queryCount second ∧ recordCount first = recordCount second ∧ drawCount first = drawCount second :=
  ⟨cell.perm.countP_eq _, cell.perm.countP_eq _, cell.perm.countP_eq _⟩

theorem Cell.continuation {Result : Type} {first second : List (Action Input)} (cell : Cell first second)
    (state : State Input Tag) (next : State Input Tag → PMF Result) :
    (run first state).bind next = (run second state).bind next := by rw [cell.sound state]

/-- Retain any earlier context and the original secret while applying the
mixed diagram. The supplied prefix need not be a deterministic computation. -/
theorem Cell.joint {Context : Type} {first second : List (Action Input)} (cell : Cell first second)
    (prefixLaw : PMF (Context × State Input Tag)) :
    (prefixLaw.bind fun original => (run first original.2).map (fun final => (original, final))) =
      (prefixLaw.bind fun original => (run second original.2).map (fun final => (original, final))) := by
  simp_rw [cell.sound]

end CryptoOracle.ProofEdits.Interaction
