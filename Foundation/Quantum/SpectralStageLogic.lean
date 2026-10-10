import Foundation.Quantum.SpectralStages

/-! The finite propositional calculus interpreted in the frame at each
future context domain. Relative implication is preserved by stage restriction;
this is not a claim about arbitrary local spectral continuous preimages. -/
namespace Foundation.Quantum.Bohr.StageLogic
open Foundation.Logic
noncomputable section
variable {A : Type} [CStarAlgebra A] (C : Bohr.Context A)

set_option backward.isDefEq.respectTransparency false

def eval (ν : Nat → StageFrame C) : Formula → StageFrame C
  | .atom n => ν n
  | .bottom => ⊥
  | .top => ⊤
  | .join P Q => eval ν P ⊔ eval ν Q
  | .meet P Q => eval ν P ⊓ eval ν Q
  | .imp P Q => eval ν P ⇨ eval ν Q

def model (ν : Nat → StageFrame C) : Model presentation where
  Carrier j := eval C ν j.1 ≤ eval C ν j.2
  operation := fun r h => match r with
    | .refl _ => le_rfl
    | .bottom _ => bot_le
    | .top _ => le_top
    | .joinLeft .. => le_sup_left
    | .joinRight .. => le_sup_right
    | .joinElim .. => sup_le (h 0) (h 1)
    | .trans .. => (h 0).trans (h 1)
    | .meetLeft .. => inf_le_left
    | .meetRight .. => inf_le_right
    | .meetIntro .. => le_inf (h 0) (h 1)
    | .impIntro .. => le_himp_iff.mpr (h 0)
    | .impElim .. => le_himp_iff.mp (h 0)

theorem sound (ν : Nat → StageFrame C) {Γ : Logic.Context presentation} {j}
    (d : Derivation presentation Γ j) (h : ∀ i, (model C ν).Carrier (Γ.claim i)) :
    (model C ν).Carrier j := d.eval (model C ν) h

theorem interpretation_substitute (ν : Nat → StageFrame C)
    {Γ Δ : Logic.Context presentation} {j} (d : Derivation presentation Γ j)
    (r : ∀ i, Derivation presentation Δ (Γ.claim i))
    (h : ∀ i, (model C ν).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model C ν) h =
      d.eval (model C ν) (fun i => (r i).eval (model C ν) h) :=
  Derivation.eval_substitute (model C ν) h d r

/-- Formula interpretation is natural along truncation of the future domain. -/
theorem eval_restrict {D : Bohr.Context A} (h : C ≤ D)
    (ν : Nat → StageFrame C) (P : Formula) :
    eval D (fun n => stageRestriction h (ν n)) P = stageRestriction h (eval C ν P) := by
  induction P with
  | atom n => rfl
  | bottom => exact (map_bot (stageRestriction h)).symm
  | top => exact (map_top (stageRestriction h)).symm
  | join P Q ihP ihQ => exact (congrArg₂ (· ⊔ ·) ihP ihQ).trans (map_sup _ _ _).symm
  | meet P Q ihP ihQ => exact (congrArg₂ (· ⊓ ·) ihP ihQ).trans (map_inf _ _ _).symm
  | imp P Q ihP ihQ => exact (congrArg₂ (· ⇨ ·) ihP ihQ).trans (stageRestriction_himp h _ _).symm

/-- Entailments valid at a stage remain valid after increasing the context. -/
theorem sound_restrict {D : Bohr.Context A} (hCD : C ≤ D)
    (ν : Nat → StageFrame C) {Γ : Logic.Context presentation} {j}
    (d : Derivation presentation Γ j)
    (h : ∀ i, (model C ν).Carrier (Γ.claim i)) :
    (model D (fun n => stageRestriction hCD (ν n))).Carrier j := by
  change eval D _ j.1 ≤ eval D _ j.2
  rw [eval_restrict, eval_restrict]
  exact OrderHomClass.mono (stageRestriction hCD) (sound C ν d h)

end
end Foundation.Quantum.Bohr.StageLogic
