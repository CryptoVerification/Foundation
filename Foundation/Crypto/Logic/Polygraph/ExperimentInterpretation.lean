import Foundation.Crypto.Logic.Polygraph.ExperimentSyntax
import Foundation.Logic.Polygraph.Structural

/-! Statistical experiment transformations interpret as genuine finite-arity
inference diagrams. The only closed rules are certified exact transformations
and supplied couplings. Triangle and weakening retain their premises; an
arbitrary final advantage bound is not a primitive rule. -/
namespace CryptoLogic.Polygraph.Experiment.Statistical

open Foundation.Probability Foundation.Logic Foundation.Logic.Polygraph
open scoped ENNReal
universe u
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

noncomputable section

structure Claim where
  left : Observed.{u}
  right : Observed.{u}
  error : ℝ≥0∞

inductive Rule where
  | exact {α : Type u} {p q : Program α} (path : ExactPath p q) (event : α → Prop)
  | coupling (left right : Observed.{u}) {Joint : Type u}
      (joint : PMF Joint) (pl : Joint → left.Outcome) (pr : Joint → right.Outcome)
      (hl : joint.map pl = left.program.eval) (hr : joint.map pr = right.program.eval)
      (bad : Joint → Prop)
      (agree : ∀ x ∈ joint.support, ¬bad x → (left.event (pl x) ↔ right.event (pr x)))
  | triangle (left middle right : Observed.{u}) (ε δ : ℝ≥0∞)
  | weaken (left right : Observed.{u}) (ε δ : ℝ≥0∞) (h : ε ≤ δ)

abbrev theory : Foundation.Logic.Presentation where
  Judgment := Claim.{u}
  Rule := Rule.{u}
  arity := fun | .exact .. | .coupling .. => 0 | .triangle .. => 2 | .weaken .. => 1
  premise := fun
    | .exact .. | .coupling .. => Fin.elim0
    | .triangle l m r ε δ => Fin.cases ⟨l, m, ε⟩ (fun _ => ⟨m, r, δ⟩)
    | .weaken l r ε _ _ => fun _ => ⟨l, r, ε⟩
  conclusion := fun
    | .exact (α := α) (p := p) (q := q) _ e => ⟨⟨α, p, e⟩, ⟨α, q, e⟩, 0⟩
    | .coupling l r joint _ _ _ _ bad _ => ⟨l, r, eventProb joint bad⟩
    | .triangle l _ r ε δ => ⟨l, r, ε + δ⟩
    | .weaken l r _ δ _ => ⟨l, r, δ⟩

def model : Foundation.Logic.Model theory where
  Carrier := fun claim => probabilityGap claim.left.probability claim.right.probability ≤ claim.error
  operation := fun rule children => match rule with
    | .exact path event => (Hop.exact path event).sound
    | .coupling _ _ joint pl pr hl hr bad agree =>
        (Hop.coupling joint pl pr hl hr bad agree).sound
    | .triangle _ _ _ _ _ =>
        (ThreeGames.probabilityGap_triangle _ _ _).trans (add_le_add (children 0) (children 1))
    | .weaken _ _ _ _ h => (children 0).trans h

def derivation : {l r : Observed.{u}} → {ε : ℝ≥0∞} → Hop l r ε →
    Foundation.Logic.Derivation theory (Foundation.Logic.Context.empty theory) ⟨l, r, ε⟩
  | _, _, _, .exact path event => .apply (T := theory) (Rule.exact path event) (fun i => Fin.elim0 i)
  | _, _, _, .coupling joint pl pr hl hr bad agree =>
      .apply (T := theory) (Rule.coupling _ _ joint pl pr hl hr bad agree) (fun i => Fin.elim0 i)
  | _, _, _, .comp p q => .apply (T := theory) (Rule.triangle _ _ _ _ _)
      (Fin.cases (derivation p) (fun _ => derivation q))
  | _, _, _, .weaken p h => .apply (T := theory) (Rule.weaken _ _ _ _ h) (fun _ => derivation p)

def diagram {l r : Observed.{u}} {ε : ℝ≥0∞} (hop : Hop l r ε) :
    Diagram theory (Foundation.Logic.Context.empty theory)
      (Foundation.Logic.Context.singleton ⟨l, r, ε⟩) := Diagram.ofDerivation (derivation hop)

theorem sound {l r : Observed.{u}} {ε : ℝ≥0∞} (hop : Hop l r ε) :
    probabilityGap l.probability r.probability ≤ ε :=
  (diagram hop).eval model (fun i => Fin.elim0 i) 0

/-- Composition becomes a two-premise triangle inference, with no discarded
intermediate obligation and with the two error terms in their original order. -/
theorem comp_tree {l m r : Observed.{u}} {ε δ : ℝ≥0∞}
    (p : Hop l m ε) (q : Hop m r δ) :
    (diagram (.comp p q)).toDerivation =
      Foundation.Logic.Derivation.apply (T := theory) (.triangle l m r ε δ)
        (Fin.cases (derivation p) (fun _ => derivation q)) := by
  unfold diagram
  rw [Diagram.toDerivation_ofDerivation]
  rfl

end
end CryptoLogic.Polygraph.Experiment.Statistical
