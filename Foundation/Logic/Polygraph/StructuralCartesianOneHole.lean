import Foundation.Logic.Polygraph.StructuralCartesianCategoryCritical

/-! Single-hole typed wire contexts remove only groupoid-unit bookkeeping
from template substitution. They introduce no additional higher generators.
The resulting argument squares use the existing one-step naturality roots. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.CategoryCritical
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

inductive Context (input output : Shape Atom) : Shape Atom → Shape Atom → Type where
  | hole : Context input output input output
  | seqLeft {a b c} (child : Context input output a b) (fixed : Wire b c) : Context input output a c
  | seqRight {a b c} (fixed : Wire a b) (child : Context input output b c) : Context input output a c
  | tensorLeft {a b c d} (child : Context input output a b) (fixed : Wire c d) : Context input output (.pair a c) (.pair b d)
  | tensorRight {a b c d} (fixed : Wire a b) (child : Context input output c d) : Context input output (.pair a c) (.pair b d)

def Context.template {u v : Shape Atom} : {a b : Shape Atom} → Context u v a b → Template u v a b
  | _, _, .hole => .hole
  | _, _, .seqLeft child fixed => .seq child.template (.fixed fixed)
  | _, _, .seqRight fixed child => .seq (.fixed fixed) child.template
  | _, _, .tensorLeft child fixed => .tensor child.template (.fixed fixed)
  | _, _, .tensorRight fixed child => .tensor (.fixed fixed) child.template

def Context.apply {u v a b : Shape Atom} (context : Context u v a b) (wire : Wire u v) : Wire a b :=
  context.template.apply wire

def Context.step {u v : Shape Atom} {p q : Wire u v} (change : Step p q) :
    {a b : Shape Atom} → (context : Context u v a b) → Step (context.apply p) (context.apply q)
  | _, _, .hole => change
  | _, _, .seqLeft child fixed => .seqLeft (child.step change) fixed
  | _, _, .seqRight fixed child => .seqRight fixed (child.step change)
  | _, _, .tensorLeft child fixed => .tensorLeft (child.step change) fixed
  | _, _, .tensorRight fixed child => .tensorRight fixed (child.step change)

theorem Context.holes {u v a b : Shape Atom} (context : Context u v a b) : context.template.holes = 1 := by
  induction context <;> simp_all only [Context.template, Template.holes, Nat.add_zero, Nat.zero_add]

def Context.changeCell {u v : Shape Atom} {p q : Wire u v} (change : Step p q) :
    {a b : Shape Atom} → (context : Context u v a b) →
      Cartesian.Higher.Homotopy (context.template.change change) (.step (context.step change))
  | _, _, .hole => .refl _
  | _, _, .seqLeft child fixed =>
      (Four.comp ((child.changeCell change).whisker (.seqLeft fixed)) (.refl _)).trans (Four.rightUnit _)
  | _, _, .seqRight fixed child =>
      (Four.comp (.refl _) ((child.changeCell change).whisker (.seqRight fixed))).trans (Four.leftUnit _)
  | _, _, .tensorLeft child fixed =>
      (Four.comp ((child.changeCell change).whisker (.tensorLeft fixed)) (.refl _)).trans (Four.rightUnit _)
  | _, _, .tensorRight fixed child =>
      (Four.comp (.refl _) ((child.changeCell change).whisker (.tensorRight fixed))).trans (Four.leftUnit _)

def oldLift {a b : Shape Atom} {p q : Wire a b} {first second : ProofTrack p q}
    (cell : Cartesian.Higher.Homotopy first second) : Cell first second := embed (UnitCritical.embed cell)

def argumentFrom {a b : Shape Atom} {p q r s : Wire a b}
    (leftStep : Step p q) (rightStep : Step r s) (beforeRoot : Step p r) (afterRoot : Step q s)
    {leftPath : ProofTrack p q} {rightPath : ProofTrack r s}
    (leftCell : Cartesian.Higher.Homotopy leftPath (.step leftStep))
    (rightCell : Cartesian.Higher.Homotopy rightPath (.step rightStep))
    (diagram : Cartesian.Higher.Homotopy
      (.comp leftPath (.step afterRoot)) (.comp (.step beforeRoot) rightPath)) :
    Cell (.comp (.step beforeRoot) (.step rightStep)) (.comp (.step leftStep) (.step afterRoot)) :=
  (Four.comp (.refl _) (oldLift rightCell).symm).trans
    ((oldLift diagram).symm.trans (Four.comp (oldLift leftCell) (.refl _)))

def Context.argument {u v a b : Shape Atom} {p q : Wire u v} (change : Step p q)
    (left right : Context u v a b) (beforeRoot : Step (left.apply p) (right.apply p))
    (afterRoot : Step (left.apply q) (right.apply q))
    (diagram : Cartesian.Higher.Homotopy
      (.comp (left.template.change change) (.step afterRoot)) (.comp (.step beforeRoot) (right.template.change change))) :
    Cell (.comp (.step beforeRoot) (.step (right.step change))) (.comp (.step (left.step change)) (.step afterRoot)) :=
  argumentFrom (left.step change) (right.step change) beforeRoot afterRoot
    (left.changeCell change) (right.changeCell change) diagram

def leftNatural {a b : Shape Atom} {p q : Wire a b} (change : Step p q) :
    Cell (two (leftUnit p) change) (two (.seqRight (.identity a) change) (leftUnit q)) :=
  Context.argument change (.seqRight (.identity a) .hole) .hole (leftUnit p) (leftUnit q)
    (argumentCell (.leftId a b) change)

def rightNatural {a b : Shape Atom} {p q : Wire a b} (change : Step p q) :
    Cell (two (rightUnit p) change) (two (.seqLeft change (.identity b)) (rightUnit q)) :=
  Context.argument change (.seqLeft .hole (.identity b)) .hole (rightUnit p) (rightUnit q)
    (argumentCell (.rightId a b) change)

def assocFirstNatural {a b c d : Shape Atom} {p p' : Wire a b} (change : Step p p')
    (q : Wire b c) (r : Wire c d) :
    Cell (two (associate p q r) (.seqLeft change (.seq q r)))
      (two (.seqLeft (.seqLeft change q) r) (associate p' q r)) :=
  Context.argument change (.seqLeft (.seqLeft .hole q) r) (.seqLeft .hole (.seq q r))
    (associate p q r) (associate p' q r) (argumentCell (.assocFirst q r) change)

def assocMiddleNatural {a b c d : Shape Atom} (p : Wire a b) {q q' : Wire b c} (change : Step q q')
    (r : Wire c d) :
    Cell (two (associate p q r) (.seqRight p (.seqLeft change r)))
      (two (.seqLeft (.seqRight p change) r) (associate p q' r)) :=
  Context.argument change (.seqLeft (.seqRight p .hole) r) (.seqRight p (.seqLeft .hole r))
    (associate p q r) (associate p q' r) (argumentCell (.assocMiddle p r) change)

def assocLastNatural {a b c d : Shape Atom} (p : Wire a b) (q : Wire b c) {r r' : Wire c d}
    (change : Step r r') :
    Cell (two (associate p q r) (.seqRight p (.seqRight q change)))
      (two (.seqRight (.seq p q) change) (associate p q r')) :=
  argumentFrom (.seqRight (.seq p q) change) (.seqRight p (.seqRight q change))
    (associate p q r) (associate p q r')
    (leftPath := (Variation.assocLast p q).left.change change)
    ((Four.comp (Four.leftUnit (.refl _)) (.refl _)).trans (Four.leftUnit _))
    ((Context.seqRight p (.seqRight q .hole)).changeCell change)
    (argumentCell (.assocLast p q) change)

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.CategoryCritical
