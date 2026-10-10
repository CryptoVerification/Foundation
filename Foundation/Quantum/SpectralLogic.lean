import Foundation.Quantum.ContextSpectrum

/-! The existing propositional presentation interpreted by actual spectral
opens. This model is distinct from the earlier context-availability model. -/
namespace Foundation.Quantum.Bohr.SpectralLogic
open Foundation.Logic
noncomputable section
variable (A : Type) [CStarAlgebra A]

set_option backward.isDefEq.respectTransparency false

def eval (ν : Nat → SpectralOpen A) : Formula → SpectralOpen A
  | .atom n => ν n
  | .bottom => ⊥
  | .top => ⊤
  | .join P Q => eval ν P ⊔ eval ν Q
  | .meet P Q => eval ν P ⊓ eval ν Q
  | .imp P Q => eval ν P ⇨ eval ν Q

def model (ν : Nat → SpectralOpen A) : Model presentation where
  Carrier j := eval A ν j.1 ≤ eval A ν j.2
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

theorem sound (ν : Nat → SpectralOpen A) {Γ : Logic.Context presentation} {j}
    (d : Derivation presentation Γ j) (h : ∀ i, (model A ν).Carrier (Γ.claim i)) :
    (model A ν).Carrier j := d.eval (model A ν) h

theorem interpretation_substitute (ν : Nat → SpectralOpen A)
    {Γ Δ : Logic.Context presentation} {j} (d : Derivation presentation Γ j)
    (r : ∀ i, Derivation presentation Δ (Γ.claim i))
    (h : ∀ i, (model A ν).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model A ν) h =
      d.eval (model A ν) (fun i => (r i).eval (model A ν) h) :=
  Derivation.eval_substitute (model A ν) h d r

end
end Foundation.Quantum.Bohr.SpectralLogic
