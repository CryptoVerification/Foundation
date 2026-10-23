import Foundation.Logic.Polygraph.StructuralCartesianCompositionTransport
import Foundation.Logic.Polygraph.StructuralCartesianOldExpansionCounts

/-! Interpret source composition proofs using the legacy eleven-law labels.
Their existing explicit expansion agrees with the actual categorical steps
up to groupoid bookkeeping. No normalizer or arbitrary parallel-path root is
used; each source step expands to exactly one new-root occurrence here. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.CategoryCritical.CompositionTransport.Legacy
variable {Atom : Type} {E : Shape Atom → Shape Atom → Type}
set_option backward.isDefEq.respectTransparency false

def edge (interpret : ∀ {a b}, E a b → Wire a b) : {a b : Shape Atom} →
    {p q : Composition.Expr E a b} → Composition.Expr.Step p q → Rewrite.Step (evaluate interpret p) (evaluate interpret q)
  | _, _, _, _, .assoc p q r => .root (.seqAssoc (evaluate interpret p) (evaluate interpret q) (evaluate interpret r))
  | _, _, _, _, .leftUnit p => .root (.leftUnit (evaluate interpret p))
  | _, _, _, _, .rightUnit p => .root (.rightUnit (evaluate interpret p))
  | _, _, _, _, .left child fixed => .seqLeft (edge interpret child) (evaluate interpret fixed)
  | _, _, _, _, .right fixed child => .seqRight (evaluate interpret fixed) (edge interpret child)

def track (interpret : ∀ {a b}, E a b → Wire a b) {a b : Shape Atom} {p q : Composition.Expr E a b}
    (path : Composition.Finite.Three p q) : Track (fun x y => Rewrite.Step x y) (evaluate interpret p) (evaluate interpret q) :=
  path.map (evaluate interpret) (fun change => edge interpret change)

def expansion (interpret : ∀ {a b}, E a b → Wire a b) : {a b : Shape Atom} →
    {p q : Composition.Expr E a b} → (change : Composition.Expr.Step p q) →
    Cartesian.Higher.Homotopy (BoundedOld.expandStep (edge interpret change)).toTrack
      (.step (CompositionTransport.edge interpret change))
  | _, _, _, _, .assoc _ _ _ => .refl _
  | _, _, _, _, .leftUnit _ => .refl _
  | _, _, _, _, .rightUnit _ => .refl _
  | _, _, _, _, .left child fixed =>
      (Four.comp ((expansion interpret child).whisker (.seqLeft (evaluate interpret fixed))) (.refl _)).trans
        (Four.rightUnit _)
  | _, _, _, _, .right fixed child =>
      (Four.comp (.refl _) ((expansion interpret child).whisker (.seqRight (evaluate interpret fixed)))).trans
        (Four.leftUnit _)

theorem expansion_roots (interpret : ∀ {a b}, E a b → Wire a b) {a b : Shape Atom}
    {p q : Composition.Expr E a b} (change : Composition.Expr.Step p q) :
    BoundedOld.roots (BoundedOld.expandStep (edge interpret change)) = 1 := by
  induction change <;> simp_all only [edge, BoundedOld.expandStep, BoundedOld.expandRoot,
    BoundedOld.roots, Nat.add_zero, Nat.zero_add]

theorem expansion_steps (interpret : ∀ {a b}, E a b → Wire a b) {a b : Shape Atom}
    {p q : Composition.Expr E a b} (change : Composition.Expr.Step p q) :
    BoundedOld.steps (BoundedOld.expandStep (edge interpret change)).toTrack = 1 := by
  rw [BoundedOld.toTrack_steps, expansion_roots]

def trackExpansion (interpret : ∀ {a b}, E a b → Wire a b) {a b : Shape Atom} :
    {p q : Composition.Expr E a b} → (path : Composition.Finite.Three p q) →
    Cartesian.Higher.Homotopy (BoundedOld.expandTrack (track interpret path)) (CompositionTransport.track interpret path)
  | _, _, .refl _ => .refl _
  | _, _, .step change => expansion interpret change
  | _, _, .comp first second => .comp (trackExpansion interpret first) (trackExpansion interpret second)
  | _, _, .inv child => .inverse (trackExpansion interpret child)

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.CategoryCritical.CompositionTransport.Legacy
