import Foundation.Logic.Polygraph.StructuralTransport

/-! Eleven directed local wire-equation forms and four placements. The two
associator cancellation equations repair a known omission of the old nine-root
language. Completeness, termination and higher critical overlaps of these
eleven forms are not asserted. No arbitrary semantic-equality root is added. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Rewrite
variable {Atom : Type}

inductive Root : {a b : Shape Atom} → Wire a b → Wire a b → Type where
  | seqAssoc {a b c d} (p : Wire a b) (q : Wire b c) (r : Wire c d) : Root (.seq (.seq p q) r) (.seq p (.seq q r))
  | leftUnit {a b} (p : Wire a b) : Root (.seq (.identity a) p) p
  | rightUnit {a b} (p : Wire a b) : Root (.seq p (.identity b)) p
  | tensorIdentity (a b) : Root (.tensor (.identity a) (.identity b)) (.identity (.pair a b))
  | interchange {a b c a' b' c'} (p : Wire a b) (q : Wire b c) (p' : Wire a' b') (q' : Wire b' c') :
      Root (.seq (.tensor p p') (.tensor q q')) (.tensor (.seq p q) (.seq p' q'))
  | copyAssoc (a) : Root (.seq (.seq (.copy a) (.tensor (.copy a) (.identity a))) (.assoc a a a))
      (.seq (.copy a) (.tensor (.identity a) (.copy a)))
  | copySwap (a) : Root (.seq (.copy a) (.swap a a)) (.copy a)
  | copyDiscardLeft (a) : Root (.seq (.seq (.copy a) (.tensor (.discard a) (.identity a))) (.leftUnit a)) (.identity a)
  | copyDiscardRight (a) : Root (.seq (.seq (.copy a) (.tensor (.identity a) (.discard a))) (.rightUnit a)) (.identity a)
  | assocUnassoc (a b c) : Root (.seq (.assoc a b c) (.unassoc a b c)) (.identity (.pair (.pair a b) c))
  | unassocAssoc (a b c) : Root (.seq (.unassoc a b c) (.assoc a b c)) (.identity (.pair a (.pair b c)))

def Root.code : {a b : Shape Atom} → {p q : Wire a b} → Root p q → Fin 11
  | _, _, _, _, .seqAssoc _ _ _ => 0
  | _, _, _, _, .leftUnit _ => 1
  | _, _, _, _, .rightUnit _ => 2
  | _, _, _, _, .tensorIdentity _ _ => 3
  | _, _, _, _, .interchange _ _ _ _ => 4
  | _, _, _, _, .copyAssoc _ => 5
  | _, _, _, _, .copySwap _ => 6
  | _, _, _, _, .copyDiscardLeft _ => 7
  | _, _, _, _, .copyDiscardRight _ => 8
  | _, _, _, _, .assocUnassoc _ _ _ => 9
  | _, _, _, _, .unassocAssoc _ _ _ => 10

theorem Root.sound {a b} {p q : Wire a b} (change : Root p q) (family : Atom → Type) (input : a.Value family) :
    p.eval family input = q.eval family input := by
  cases change <;> rfl

inductive Step : {a b : Shape Atom} → Wire a b → Wire a b → Type where
  | root {a b} {p q : Wire a b} (change : Root p q) : Step p q
  | seqLeft {a b c} {p p' : Wire a b} (change : Step p p') (q : Wire b c) : Step (.seq p q) (.seq p' q)
  | seqRight {a b c} (p : Wire a b) {q q' : Wire b c} (change : Step q q') : Step (.seq p q) (.seq p q')
  | tensorLeft {a b c d} {p p' : Wire a b} (change : Step p p') (q : Wire c d) : Step (.tensor p q) (.tensor p' q)
  | tensorRight {a b c d} (p : Wire a b) {q q' : Wire c d} (change : Step q q') : Step (.tensor p q) (.tensor p q')

theorem Step.sound {a b} {p q : Wire a b} (change : Step p q) (family : Atom → Type) (input : a.Value family) :
    p.eval family input = q.eval family input := by
  induction change with
  | root change => exact change.sound family input
  | seqLeft change fixed ih => exact congrArg (fixed.eval family) (ih input)
  | seqRight fixed change ih => exact ih (fixed.eval family input)
  | tensorLeft change fixed ih => exact congrArg (fun x => (x, fixed.eval family input.2)) (ih input.1)
  | tensorRight fixed change ih => exact congrArg (fun x => (fixed.eval family input.1, x)) (ih input.2)

/-- Only an over-approximation, used to rule out rewrites of a bare copy.
It is not a complete redex detector. -/
def composite : {a b : Shape Atom} → Wire a b → Bool
  | _, _, .seq _ _ | _, _, .tensor _ _ => true
  | _, _, _ => false

theorem Step.source_composite {a b : Shape Atom} {p q : Wire a b} (change : Step p q) : composite p = true := by
  cases change with
  | root root => cases root <;> rfl
  | seqLeft | seqRight | tensorLeft | tensorRight => rfl

end Foundation.Logic.Polygraph.StructuralTransport.Rewrite
