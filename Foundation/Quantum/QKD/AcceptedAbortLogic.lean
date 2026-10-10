import Foundation.Quantum.QKD.AcceptedAbortComposition
import Foundation.Quantum.QKD.CommonKeyLogic

/-! A finite object logic that first combines correctness and secrecy, then
joins the unchanged abort branch. It interprets the conclusion as the existing
IdealKey.Secure of a constructed full normalized density. -/
namespace Foundation.Quantum.QKD.AcceptedAbortLogic
noncomputable section
open Foundation.Logic Subnormalized
set_option backward.isDefEq.respectTransparency false

inductive Claim where
  | correctness (state : Nat) (δ : ℝ)
  | secrecy (state : Nat) (ε : ℝ)
  | accepted (state : Nat) (η : ℝ)
  | secure (state : Nat) (η : ℝ)

inductive Rule where
  | compose (state : Nat) (δ ε : ℝ)
  | finish (state : Nat) (η : ℝ)

abbrev presentation : Presentation where
  Judgment := Claim
  Rule := Rule
  arity := fun | .compose .. => 2 | .finish .. => 1
  premise := fun
    | .compose s δ ε => fun i => if i = 0 then .correctness s δ else .secrecy s ε
    | .finish s η => fun _ => .accepted s η
  conclusion := fun
    | .compose s δ ε => .accepted s (δ+ε)
    | .finish s η => .secure s η

variable {T : Type} [Fintype T] [DecidableEq T] {length : Nat} {e : Space}

def model (ρ : Nat → State (AcceptedAbort.AcceptedLabel T length) e)
    (σ : Nat → State T e) (hmass : ∀ s, mass (ρ s) + mass (σ s) = 1) : Model presentation where
  Carrier := fun
    | .correctness s δ => CommonKey.correctnessError (ρ s) ≤ δ
    | .secrecy s ε => OperatorApprox (joint (CommonKey.aliceView (ρ s)))
        (joint (CommonKey.uniformize (CommonKey.aliceView (ρ s)))) ε
    | .accepted s η => OperatorApprox (joint (ρ s)) (joint (CommonKey.ideal (ρ s))) η
    | .secure s η => IdealKey.Secure (AcceptedAbort.state (ρ s) (σ s) (hmass s)) η
  operation := fun rule hs => by
    cases rule with
    | compose s δ ε => exact CommonKey.compose (ρ s) δ ε (hs 0) (hs 1)
    | finish s η => exact AcceptedAbort.secure_of_common (ρ s) (σ s) (hmass s) η (hs 0)

theorem sound (ρ : Nat → State (AcceptedAbort.AcceptedLabel T length) e)
    (σ : Nat → State T e) (hmass : ∀ s, mass (ρ s) + mass (σ s) = 1)
    {Γ : Logic.Context presentation} {j} (d : Derivation presentation Γ j)
    (hs : ∀ i, (model ρ σ hmass).Carrier (Γ.claim i)) : (model ρ σ hmass).Carrier j := d.eval _ hs

theorem interpretation_substitute (ρ : Nat → State (AcceptedAbort.AcceptedLabel T length) e)
    (σ : Nat → State T e) (hmass : ∀ s, mass (ρ s) + mass (σ s) = 1)
    {Γ Δ : Logic.Context presentation} {j} (d : Derivation presentation Γ j)
    (f : ∀ i, Derivation presentation Δ (Γ.claim i))
    (hs : ∀ i, (model ρ σ hmass).Carrier (Δ.claim i)) :
    (d.substitute f).eval (model ρ σ hmass) hs =
      d.eval (model ρ σ hmass) (fun i => (f i).eval (model ρ σ hmass) hs) :=
  Derivation.eval_substitute _ hs d f

def assumptions (s : Nat) (δ ε : ℝ) : Logic.Context presentation :=
  ⟨2,fun i => if i = 0 then .correctness s δ else .secrecy s ε⟩

def proof (s : Nat) (δ ε : ℝ) :
    Derivation presentation (assumptions s δ ε) (.secure s (δ+ε)) := by
  apply Derivation.apply (T := presentation) (.finish s (δ+ε))
  intro _
  apply Derivation.apply (T := presentation) (.compose s δ ε)
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact .hypothesis ⟨0,by change 0 < 2; decide⟩
  · have hi1 : i = 1 := by omega
    subst i
    exact .hypothesis ⟨1,by change 1 < 2; decide⟩

end
end Foundation.Quantum.QKD.AcceptedAbortLogic
