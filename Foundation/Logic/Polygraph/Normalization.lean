import Foundation.Logic.Polygraph.Rewriting
import Mathlib.Tactic.Common

/-! Convergent rewriting of typed composition expressions. Edges may themselves
be multi-input diagrams. Only association and units are oriented here; no
cryptographic reduction, tensor interchange, or contraction is oriented. -/
namespace Foundation.Logic.Polygraph.Composition

universe u v
variable {O : Type u} (E : O → O → Type v)

inductive Expr : O → O → Type (max u v) where
  | identity (a) : Expr a a
  | atom {a b} : E a b → Expr a b
  | seq {a b c} : Expr a b → Expr b c → Expr a c

inductive Chain : O → O → Type (max u v) where
  | nil (a) : Chain a a
  | cons {a b c} : E a b → Chain b c → Chain a c

variable {E}

namespace Chain
variable {a b c d : O}

def append : {a b c : O} → Chain E a b → Chain E b c → Chain E a c
  | _, _, _, .nil _, ys => ys
  | _, _, _, .cons e xs, ys => .cons e (append xs ys)

@[simp] theorem append_nil (xs : Chain E a b) : append xs (.nil b) = xs := by
  induction xs with
  | nil => rfl
  | cons e xs ih => exact congrArg (cons e) ih

theorem append_assoc (xs : Chain E a b) (ys : Chain E b c) (zs : Chain E c d) :
    append (append xs ys) zs = append xs (append ys zs) := by
  induction xs with
  | nil => rfl
  | cons e xs ih => exact congrArg (cons e) (ih ys)

def reflect : {a b : O} → Chain E a b → Expr E a b
  | _, _, .nil a => .identity a
  | _, _, .cons e (.nil _) => .atom e
  | _, _, .cons e (.cons f xs) => .seq (.atom e) (reflect (.cons f xs))

end Chain

namespace Expr
variable {a b c d : O}

def flatten : {a b : O} → Expr E a b → Chain E a b
  | _, _, .identity a => .nil a
  | _, _, .atom e => .cons e (.nil _)
  | _, _, .seq f g => (flatten f).append (flatten g)

@[simp] theorem flatten_reflect (xs : Chain E a b) : xs.reflect.flatten = xs := by
  induction xs with
  | nil => rfl
  | cons e xs ih => cases xs <;> simp_all [Chain.reflect, flatten, Chain.append]

def normal (e : Expr E a b) : Expr E a b := e.flatten.reflect

@[simp] theorem normal_idempotent (e : Expr E a b) : normal (normal e) = normal e := by
  simp [normal]

def size : {a b : O} → Expr E a b → Nat
  | _, _, .identity _ | _, _, .atom _ => 1
  | _, _, .seq f g => size f + size g + 1

theorem size_pos (e : Expr E a b) : 0 < e.size := by cases e <;> simp [size]

def weight : {a b : O} → Expr E a b → Nat
  | _, _, .identity _ | _, _, .atom _ => 0
  | _, _, .seq f g => weight f + weight g + size f

inductive Step : {a b : O} → Expr E a b → Expr E a b → Type (max u v) where
  | assoc {a b c d : O} (f : Expr E a b) (g : Expr E b c) (h : Expr E c d) :
      Step (.seq (.seq f g) h) (.seq f (.seq g h))
  | leftUnit {a b : O} (f : Expr E a b) : Step (.seq (.identity a) f) f
  | rightUnit {a b : O} (f : Expr E a b) : Step (.seq f (.identity b)) f
  | left {a b c : O} {f f' : Expr E a b} (s : Step f f') (g : Expr E b c) :
      Step (.seq f g) (.seq f' g)
  | right {a b c : O} (f : Expr E a b) {g g' : Expr E b c} (s : Step g g') :
      Step (.seq f g) (.seq f g')

theorem Step.decreases {f g : Expr E a b} (s : Step f g) :
    g.weight < f.weight ∧ g.size ≤ f.size := by
  induction s with
  | assoc f g h => simp only [weight, size]; omega
  | leftUnit f => simp only [weight, size]; omega
  | rightUnit f => have := size_pos f; simp only [weight, size]; omega
  | left s g ih => simp only [weight, size]; omega
  | right f s ih => simp only [weight, size]; omega

/-- No infinite forward sequence of structural rewrites exists. -/
theorem terminating (a b : O) :
    WellFounded (fun g f : Expr E a b => Nonempty (Step f g)) :=
  Subrelation.wf (fun ⟨s⟩ => s.decreases.1) (measure weight).wf

theorem Step.flatten_eq {f g : Expr E a b} (s : Step f g) : f.flatten = g.flatten := by
  induction s with
  | assoc f g h => exact Chain.append_assoc _ _ _
  | leftUnit => rfl
  | rightUnit => exact Chain.append_nil _
  | left s g ih => exact congrArg (fun x => x.append g.flatten) ih
  | right f s ih => exact congrArg (fun x => f.flatten.append x) ih

/-- Reflected chains have no forward structural redex. In particular the
computed normal form is irreducible, not merely an idempotent representative. -/
theorem reflect_irreducible (xs : Chain E a b) {g : Expr E a b}
    (step : Step xs.reflect g) : False := by
  induction xs with
  | nil => cases step
  | cons e xs ih =>
      cases xs with
      | nil => cases step
      | cons f ys =>
          cases ys with
          | nil =>
              cases step with
              | left s _ => cases s
              | right _ s => cases s
          | cons h zs =>
              cases step with
              | left s _ => cases s
              | right _ s => exact ih s

theorem normal_irreducible (f : Expr E a b) {g : Expr E a b}
    (step : Step f.normal g) : False := reflect_irreducible f.flatten step

abbrev Path (f g : Expr E a b) := RewritePath (@Step O E a b) f g

def Path.left {f f' : Expr E a b} (p : Path f f') (g : Expr E b c) :
    Path (.seq f g) (.seq f' g) :=
  p.map (S := fun x y => Step x y) (fun f => Expr.seq f g) (fun s => Step.left s g)

def Path.right (f : Expr E a b) {g g' : Expr E b c} (p : Path g g') :
    Path (.seq f g) (.seq f g') :=
  p.map (S := fun x y => Step x y) (fun g => Expr.seq f g) (fun s => Step.right f s)

def appendPath {a b c : O} (xs : Chain E a b) (ys : Chain E b c) :
    Path (.seq xs.reflect ys.reflect) (xs.append ys).reflect := by
  cases xs with
  | nil => exact .single (.leftUnit _)
  | cons e xs =>
      cases ys with
      | nil => simpa only [Chain.reflect, Chain.append_nil] using
          (RewritePath.single (Step.rightUnit (Chain.cons e xs).reflect))
      | cons f ys =>
          cases xs with
          | nil => exact .refl _
          | cons h xs =>
              exact (RewritePath.single (Step.assoc (.atom e) _ _)).comp
                (Path.right (.atom e) (appendPath (.cons h xs) (.cons f ys)))

/-- This computes a directed path, rather than only asserting normal-form equality. -/
def normalizePath : {a b : O} → (f : Expr E a b) → Path f f.normal
  | _, _, .identity _ => .refl _
  | _, _, .atom _ => .refl _
  | _, _, .seq f g => ((normalizePath f).left g).comp
      ((Path.right f.normal (normalizePath g)).comp (appendPath f.flatten g.flatten))

theorem Path.flatten_eq {f g : Expr E a b} (p : Path f g) : f.flatten = g.flatten := by
  induction p with
  | refl => rfl
  | cons s p ih => exact s.flatten_eq.trans ih

/-- Every fork, including nested and disjoint rewrites, joins at the computed
normal form. This establishes confluence without assuming critical coverage. -/
theorem confluent {f g h : Expr E a b} (p : Path f g) (q : Path f h) :
    ∃ k, Nonempty (Path g k) ∧ Nonempty (Path h k) := by
  refine ⟨f.normal, ?_, ?_⟩
  · have he : g.normal = f.normal := congrArg Chain.reflect p.flatten_eq.symm
    exact ⟨he ▸ normalizePath g⟩
  · have he : h.normal = f.normal := congrArg Chain.reflect q.flatten_eq.symm
    exact ⟨he ▸ normalizePath h⟩

end Expr
end Foundation.Logic.Polygraph.Composition
