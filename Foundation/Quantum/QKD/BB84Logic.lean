import Foundation.Quantum.QKD.BB84KeyState
import Foundation.Logic.Presentation

/-! A syntax-level zero-disturbance BB84 inference rule. Its premises refer to
physical measurement probabilities. This is deliberately a single-signal
lemma, not a claim of finite-key QKD security. The rule is our reconstruction,
not a proof calculus explicitly presented in Heunen's thesis. -/
namespace Foundation.Quantum.QKD.BB84Logic
open Foundation.Logic
noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive Claim where
  | zTest : Nat → Fin 2 → Claim
  | xPlusTest : Nat → Claim
  | noInformation : Nat → Claim
  | idealKey : Nat → Claim

inductive Rule where
  | complementaryTests : Nat → Rule
  | complementaryKeyTests : Nat → Rule

def testClaim (n : Nat) (i : Fin 3) : Claim :=
  if i = 0 then .zTest n 0 else if i = 1 then .zTest n 1 else .xPlusTest n

abbrev presentation : Presentation where
  Judgment := Claim
  Rule := Rule
  arity _ := 3
  premise | .complementaryTests n | .complementaryKeyTests n => testClaim n
  conclusion
    | .complementaryTests n => .noInformation n
    | .complementaryKeyTests n => .idealKey n

variable {e : Space}

def meaning (σ : Nat → BB84Attack e) : Claim → Prop
  | .zTest n b => (basisEffect .bit (1 - b)).probability
      ((σ n).bobChannel.run (basisDensity .bit b)) = 0
  | .xPlusTest n => (measurementEffect .X 1).probability
      ((σ n).bobChannel.run (prepare .X 0)) = 0
  | .noInformation n => ∀ (E : Effect e) (b c : Fin 2),
      E.probability ((σ n).environmentState b) = E.probability ((σ n).environmentState c)
  | .idealKey n => (keyEnvironment (σ n).environmentState).matrix =
      (tensorDensity uniformBit ((σ n).environmentState 0)).matrix

def model (σ : Nat → BB84Attack e) : Model presentation where
  Carrier := meaning σ
  operation := fun r h => by
    cases r with
    | complementaryTests n =>
      have hz0 : (basisEffect .bit 1).probability
          ((σ n).bobChannel.run (basisDensity .bit 0)) = 0 := h 0
      have hz1 : (basisEffect .bit 0).probability
          ((σ n).bobChannel.run (basisDensity .bit 1)) = 0 := h 1
      exact (σ n).environment_independent_of_tests hz0 hz1 (h 2)
    | complementaryKeyTests n =>
      have hz0 : (basisEffect .bit 1).probability
          ((σ n).bobChannel.run (basisDensity .bit 0)) = 0 := h 0
      have hz1 : (basisEffect .bit 0).probability
          ((σ n).bobChannel.run (basisDensity .bit 1)) = 0 := h 1
      exact (σ n).key_state_independent_of_tests hz0 hz1 (h 2)

theorem sound (σ : Nat → BB84Attack e) {Γ : Context presentation} {j}
    (d : Derivation presentation Γ j) (h : ∀ i, (model σ).Carrier (Γ.claim i)) :
    (model σ).Carrier j := d.eval (model σ) h

def testContext (n : Nat) : Context presentation :=
  ⟨3, presentation.premise (.complementaryTests n)⟩

/-- The three test assumptions are explicitly bound in a finite context. -/
def complementaryProof (n : Nat) : Derivation presentation (testContext n) (.noInformation n) :=
  .apply (T := presentation) (.complementaryTests n) (fun i => .hypothesis (T := presentation) (Γ := testContext n) i)

/-- The same three syntactic premises also derive the independent ideal key state. -/
def idealKeyProof (n : Nat) : Derivation presentation (testContext n) (.idealKey n) :=
  .apply (T := presentation) (.complementaryKeyTests n)
    (fun i => .hypothesis (T := presentation) (Γ := testContext n) i)

theorem interpretation_substitute (σ : Nat → BB84Attack e)
    {Γ Δ : Context presentation} {j} (d : Derivation presentation Γ j)
    (r : ∀ i, Derivation presentation Δ (Γ.claim i))
    (h : ∀ i, (model σ).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model σ) h =
      d.eval (model σ) (fun i => (r i).eval (model σ) h) :=
  Derivation.eval_substitute (model σ) h d r

end
end Foundation.Quantum.QKD.BB84Logic
