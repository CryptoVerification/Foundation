import Foundation.Quantum.QKD.AcceptedAbortLogic

/-! Exact decomposition of a physical classical branch, retaining positive
quantum blocks and their original mass. The accepted/abort comparison applies
to the output of the specified branching function. -/
namespace Foundation.Quantum.QKD.ClassicalBranching
noncomputable section
open Subnormalized AcceptedAbort
set_option backward.isDefEq.respectTransparency false
variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T] {e : Space} {length : Nat}

/-- Exact operator partition, rather than a statement about probabilities only. -/
theorem joint_partition [DecidableEq Y] (ρ : State X e) (P : X → Prop) [DecidablePred P]
    (f g : X → Y) :
    joint (relabel ρ (fun x => if P x then f x else g x)) =
      joint (relabel (restrict ρ P) f) + joint (relabel (restrict ρ (fun x => ¬ P x)) g) := by
  have hb (y : Y) : (relabel ρ (fun x => if P x then f x else g x)).block y =
      (relabel (restrict ρ P) f).block y + (relabel (restrict ρ (fun x => ¬ P x)) g).block y := by
    simp only [relabel, restrict, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : P x <;> simp [hx]
  apply Matrix.ext
  intro ⟨r,i⟩ ⟨s,j⟩
  obtain ⟨y,rfl⟩ := (Fintype.equivFin Y).surjective r
  obtain ⟨z,rfl⟩ := (Fintype.equivFin Y).surjective s
  rw [joint_block (relabel ρ (fun x => if P x then f x else g x)) y z i j]
  simp only [Matrix.add_apply]
  rw [joint_block (relabel (restrict ρ P) f) y z i j,
    joint_block (relabel (restrict ρ (fun x => ¬ P x)) g) y z i j]
  by_cases h : y = z
  · subst z
    simp only [ite_true, hb, Matrix.add_apply]
  · simp [h]

/-- Accepted and abort labels give exactly the earlier normalized output
construction once the source has mass one. -/
theorem final_partition [DecidableEq T] (ρ : State X e) (P : X → Prop) [DecidablePred P]
    (f : X → AcceptedLabel T length) (g : X → T) :
    joint (relabel ρ (fun x => if P x then acceptLabel (f x) else abortLabel (g x))) =
      joint (relabel (relabel (restrict ρ P) f) acceptLabel) +
        joint (relabel (relabel (restrict ρ (fun x => ¬ P x)) g) (abortLabel (length := length))) := by
  classical
  rw [relabel_comp, relabel_comp]
  exact joint_partition ρ P (acceptLabel ∘ f) ((abortLabel (length := length)) ∘ g)

/-- The partition preserves the full mass, without dividing by acceptance. -/
theorem final_mass [DecidableEq T] (ρ : State X e) (P : X → Prop) [DecidablePred P]
    (f : X → AcceptedLabel T length) (g : X → T) :
    mass (relabel (restrict ρ P) f) + mass (relabel (restrict ρ (fun x => ¬ P x)) g) = mass ρ := by
  rw [mass_relabel, mass_relabel, mass_partition]

end
end Foundation.Quantum.QKD.ClassicalBranching
