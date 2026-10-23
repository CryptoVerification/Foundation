import Foundation.Examples.PolygraphLogic
import Foundation.Logic.Polygraph.DiagramNormalization
import Foundation.Logic.Polygraph.HigherPresentation
import Foundation.Logic.Polygraph.Category

/-! Concrete three-paths and four-dimensional comparisons. The pentagon's
two paths have different lengths, and are compared by a constructed four-cell,
not by proof irrelevance. These are synthetic logical examples. -/
namespace Foundation.Logic.Polygraph.Examples.Coherence

open Foundation.Logic.Polygraph.Composition
set_option backward.isDefEq.respectTransparency false
abbrev Edge (_ _ : Unit) := Nat
abbrev Expression := Expr Edge () ()

def a : Expression := .atom 1
def b : Expression := .atom 2
def c : Expression := .atom 3
def d : Expression := .atom 4

def start : Expression := .seq (.seq (.seq a b) c) d
def finish : Expression := .seq a (.seq b (.seq c d))

def upper : Expr.Path start finish :=
  (RewritePath.single (Expr.Step.assoc (.seq a b) c d)).comp
    (RewritePath.single (Expr.Step.assoc a b (.seq c d)))

def lower : Expr.Path start finish :=
  (RewritePath.single (Expr.Step.left (Expr.Step.assoc a b c) d)).comp
    ((RewritePath.single (Expr.Step.assoc a (.seq b c) d)).comp
      (RewritePath.single (Expr.Step.right a (Expr.Step.assoc b c d))))

example : upper.length = 2 := rfl
example : lower.length = 3 := rfl
example : upper ≠ lower := by
  intro h
  have hl := congrArg RewritePath.length h
  change 2 = 3 at hl
  contradiction

def system := Expr.normalizer (E := Edge) () ()
def key := start.flatten

def upper3 := Track.ofPath (system.liftPath upper (k := key) rfl)
def lower3 := Track.ofPath (system.liftPath lower (k := key) rfl)

/-- The pentagon comparison uses only the normalizing single-step squares
and the explicit groupoid laws in the four-dimensional completion. -/
def pentagon : system.Cell4 upper3 lower3 := system.coherent upper3 lower3

def unitStart : Expression := .seq (.seq (.identity ()) a) b
def unitFinish : Expression := .seq a b
def unitShort : Expr.Path unitStart unitFinish :=
  .single (.left (.leftUnit a) b)
def unitLong : Expr.Path unitStart unitFinish :=
  (RewritePath.single (Expr.Step.assoc (.identity ()) a b)).comp
    (.single (.leftUnit (.seq a b)))

def unitCoherence : system.Cell4
    (Track.ofPath (system.liftPath unitShort (k := unitStart.flatten) rfl))
    (Track.ofPath (system.liftPath unitLong (k := unitStart.flatten) rfl)) :=
  system.coherent _ _

example : WellFounded (fun g f : Expression => Nonempty (Expr.Step f g)) := Expr.terminating () ()

example : ∃ k, Nonempty (Expr.Path finish k) ∧ Nonempty (Expr.Path finish k) :=
  Expr.confluent upper lower

/-- info: 7 -/
#guard_msgs in
#eval start.normal.size

def noisy : Diagram theory one one :=
  .seq (.seq (.identity one) shared) (.identity one)

/-- info: 6 -/
#guard_msgs in
#eval (Diagram.normalize noisy).eval numeric (fun _ => 3) 0

example : (Diagram.normalize noisy).toForest = noisy.toForest := Diagram.normalize_forest _

example : Cell.ofDiagram (Diagram.seq (.identity one) shared) = Cell.ofDiagram shared := by
  rw [← Cell.seq_ofDiagram]
  exact Cell.identity_seq _

example : Cell.ofDiagram (Diagram.generator (T := theory) Rule.unary) ≠
    Cell.ofDiagram (Diagram.generator (T := theory) Rule.alternative) := by
  intro h
  have he := congrArg (fun x => Cell.eval numeric x (fun _ => 0) 0) h
  change 0 + 1 = 0 + 2 at he
  contradiction

def unary : Diagram theory one one := .generator (T := theory) Rule.unary
def alternative : Diagram theory one one := .generator (T := theory) Rule.alternative

inductive Fusion : {Γ Δ : Logic.Context theory} → Diagram theory Γ Δ →
    Diagram theory Γ Δ → Type where
  | fuse : Fusion (.seq unary unary) alternative

def fusionPresentation : Presentation3 theory where
  Generator := Fusion

theorem fusion_numeric : fusionPresentation.Respects numeric := by
  intro Γ Δ f g generator env
  cases generator
  funext i
  rfl

def fusionPath : fusionPresentation.Cell3 (.seq unary unary) alternative :=
  .step (.generator .fuse)

def fusionFour : Presentation4 fusionPresentation where
  Generator := fun _ _ => PEmpty

def fusionReflexivity : fusionFour.Cell4 fusionPath fusionPath := .base (.refl _)

def fusionInContext := Presentation4.Cell4.seqLeft (Q := fusionFour)
  fusionReflexivity (.identity one)

def fusionInTuple := Presentation4.Cell4.tupleAt (Q := fusionFour)
  (Δ := one) (fun _ => unary) 0 fusionReflexivity

example (env : Environment numeric one) :
    (Diagram.seq unary unary).eval numeric env = alternative.eval numeric env :=
  Presentation3.Cell3.eval_eq fusionPresentation numeric fusion_numeric fusionPath env

/-- The new generator does not make the underlying free two-cells equal. -/
example : Cell.ofDiagram (Diagram.seq unary unary) ≠ Cell.ofDiagram alternative := by
  intro h
  have hf := (Cell.ofDiagram_eq_iff _ _).mp h
  have ht := congrFun hf 0
  dsimp [unary, alternative, Diagram.toForest, Logic.Derivation.substitute] at ht
  cases ht

-- Different boundaries and different parallelism levels are rejected.
#guard_msgs (drop info) in
#check_failure (Expr.Step.assoc a b c : Expr.Step a b)

#guard_msgs (drop info) in
#check_failure (pentagon : system.Cell4 upper3 upper3)

end Foundation.Logic.Polygraph.Examples.Coherence
