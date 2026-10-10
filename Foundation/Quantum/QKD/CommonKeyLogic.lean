import Foundation.Quantum.QKD.CommonKeyComposition
import Foundation.Logic.Presentation

/-! Finite rules for composing accepted-branch correctness and secrecy into
a bound on the common-key ideal. All judgments have actual quantum-operator
interpretations; an arbitrary semantic-truth rule is not provided. -/
namespace Foundation.Quantum.QKD.CommonKeyLogic
noncomputable section
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false

inductive Claim where
  | correctness (state : Nat) (δ : ℝ)
  | secrecy (state : Nat) (ε : ℝ)
  | commonKey (state : Nat) (ε : ℝ)

inductive Rule where
  | compose (state : Nat) (δ ε : ℝ)
  | weaken (state : Nat) (ε η : ℝ) (h : ε ≤ η)

abbrev presentation : Presentation where
  Judgment := Claim
  Rule := Rule
  arity := fun | .compose .. => 2 | _ => 1
  premise := fun
    | .compose s δ ε => fun i => if i = 0 then .correctness s δ else .secrecy s ε
    | .weaken s ε _ _ => fun _ => .commonKey s ε
  conclusion := fun
    | .compose s δ ε => .commonKey s (δ+ε)
    | .weaken s _ η _ => .commonKey s η

variable {K T : Type} [Fintype K] [Nonempty K] [Fintype T] [DecidableEq K] [DecidableEq T] {e : Space}

def model (ρ : Nat → Subnormalized.State ((K × K) × T) e) : Model presentation where
  Carrier := fun
    | .correctness s δ => CommonKey.correctnessError (ρ s) ≤ δ
    | .secrecy s ε => OperatorApprox (Subnormalized.joint (CommonKey.aliceView (ρ s)))
        (Subnormalized.joint (CommonKey.uniformize (CommonKey.aliceView (ρ s)))) ε
    | .commonKey s ε => OperatorApprox (Subnormalized.joint (ρ s)) (Subnormalized.joint (CommonKey.ideal (ρ s))) ε
  operation := fun rule hs => by
    cases rule with
    | compose s δ ε => exact CommonKey.compose (ρ s) δ ε (hs 0) (hs 1)
    | weaken s ε η hεη => exact (hs 0).weaken hεη

theorem sound (ρ : Nat → Subnormalized.State ((K × K) × T) e)
    {Γ : Logic.Context presentation} {j} (d : Derivation presentation Γ j)
    (hs : ∀ i, (model ρ).Carrier (Γ.claim i)) : (model ρ).Carrier j := d.eval _ hs

theorem interpretation_substitute (ρ : Nat → Subnormalized.State ((K × K) × T) e)
    {Γ Δ : Logic.Context presentation} {j} (d : Derivation presentation Γ j)
    (f : ∀ i, Derivation presentation Δ (Γ.claim i))
    (hs : ∀ i, (model ρ).Carrier (Δ.claim i)) :
    (d.substitute f).eval (model ρ) hs = d.eval (model ρ) (fun i => (f i).eval (model ρ) hs) :=
  Derivation.eval_substitute _ hs d f

def assumptions (s : Nat) (δ ε : ℝ) : Logic.Context presentation :=
  ⟨2,fun i => if i = 0 then .correctness s δ else .secrecy s ε⟩

def proof (s : Nat) (δ ε η : ℝ) (hη : δ+ε ≤ η) :
    Derivation presentation (assumptions s δ ε) (.commonKey s η) := by
  apply Derivation.apply (T := presentation) (.weaken s (δ+ε) η hη)
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
end Foundation.Quantum.QKD.CommonKeyLogic
