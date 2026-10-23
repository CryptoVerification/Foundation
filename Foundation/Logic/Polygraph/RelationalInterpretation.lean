import Foundation.Logic.Polygraph.CartesianCoherence
import Foundation.Logic.Polygraph.Translation

/-! A local-to-global relational interpretation theorem for the full diagram
syntax. Relations may express directed resource improvement as well as
semantic equality. They must be preserved by every rule, including the
interaction with related input witnesses; pointwise replacement alone is
insufficient. Structural paths can be chosen independently on both sides. -/
namespace Foundation.Logic.Polygraph
universe j r v w
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
variable {T : Presentation.{j, r}}

structure InterpretationRelation (M : Model.{j, r, v} T) (N : Model.{j, r, w} T) where
  Rel : ∀ A, M.Carrier A → N.Carrier A → Prop
  rule : ∀ (r : T.Rule) (left : ∀ i, M.Carrier (T.premise r i))
      (right : ∀ i, N.Carrier (T.premise r i)), (∀ i, Rel _ (left i) (right i)) →
    Rel _ (M.operation r left) (N.operation r right)

namespace InterpretationRelation
variable {M : Model.{j, r, v} T} {N : Model.{j, r, w} T} (R : InterpretationRelation M N)

theorem derivation {Γ : Logic.Context T} {A} (d : Logic.Derivation T Γ A)
    (left : Environment M Γ) (right : Environment N Γ)
    (h : ∀ i, R.Rel _ (left i) (right i)) : R.Rel _ (d.eval M left) (d.eval N right) := by
  induction d with
  | hypothesis i => exact h i
  | apply rule children ih => exact R.rule rule _ _ ih

/-- One obligation per rule proves the relation for every raw diagram,
including arbitrary horizontal composition, shared outputs and empty outputs. -/
theorem diagram {Γ Δ : Logic.Context T} (d : Diagram T Γ Δ)
    (left : Environment M Γ) (right : Environment N Γ)
    (h : ∀ i, R.Rel _ (left i) (right i)) (i : Fin Δ.length) :
    R.Rel _ (d.eval M left i) (d.eval N right i) := by
  rw [← Diagram.eval_toForest, ← Diagram.eval_toForest]
  exact R.derivation (d.toForest i) left right h

/-- Optimize and choose structural routes independently in the two
interpretations. Finite Cartesian coherence compares parallel route choices;
this theorem separately transports their endpoint resource relation. -/
theorem structural {Γ Δ : Logic.Context T} {d e f : Diagram T Γ Δ}
    (p : Diagram.Cell3 d e) (q : Diagram.Cell3 d f)
    (left : Environment M Γ) (right : Environment N Γ)
    (h : ∀ i, R.Rel _ (left i) (right i)) (i : Fin Δ.length) :
    R.Rel _ (e.eval M left i) (f.eval N right i) := by
  rw [← p.eval_eq M left, ← q.eval_eq N right]
  exact R.diagram d left right h i

/-- The same local relational contract handles macro expansion. The
expanded target is interpreted in its own model, not a numerical proxy. -/
theorem expanded {U : Presentation} (t : Logic.Translation T U) (Q : Model U)
    (R : InterpretationRelation M (t.pullback Q))
    {Γ Δ : Logic.Context T} (d : Diagram T Γ Δ)
    (left : Environment M Γ) (right : Environment (t.pullback Q) Γ)
    (h : ∀ i, R.Rel _ (left i) (right i)) (i : Fin Δ.length) :
    R.Rel _ (d.eval M left i) ((Translation.diagram t d).eval Q right i) := by
  rw [Translation.eval_diagram]
  exact R.diagram d left right h i

end InterpretationRelation
end Foundation.Logic.Polygraph
