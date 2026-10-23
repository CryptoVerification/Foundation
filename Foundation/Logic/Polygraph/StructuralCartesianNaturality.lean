import Foundation.Logic.Polygraph.StructuralCartesianTemplates

/-! Sixteen explicit argument-naturality forms for the eighteen cartesian
root equations. Duplicated/erased arguments are represented by two/zero holes.
No normalizer or arbitrary pair of proof paths occurs in a root diagram. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

inductive Variation : Shape Atom → Shape Atom → Shape Atom → Shape Atom → Type where
  | assocFirst {a b c d} (q : Wire b c) (r : Wire c d) : Variation a b a d
  | assocMiddle {a b c d} (p : Wire a b) (r : Wire c d) : Variation b c a d
  | assocLast {a b c d} (p : Wire a b) (q : Wire b c) : Variation c d a d
  | leftId (a b : Shape Atom) : Variation a b a b
  | rightId (a b : Shape Atom) : Variation a b a b
  | betaFstFirst {a b c} (q : Wire a c) : Variation a b a b
  | betaFstLast {a b c} (p : Wire a b) : Variation a c a b
  | betaSndFirst {a b c} (q : Wire a c) : Variation a b a c
  | betaSndLast {a b c} (p : Wire a b) : Variation a c a c
  | eta (a b c : Shape Atom) : Variation a (.pair b c) a (.pair b c)
  | discard (a b : Shape Atom) : Variation a b a .unit
  | forkFirst {a b c d} (q : Wire b c) (r : Wire b d) : Variation a b a (.pair c d)
  | forkMiddle {a b c d} (p : Wire a b) (r : Wire b d) : Variation b c a (.pair c d)
  | forkLast {a b c d} (p : Wire a b) (q : Wire b c) : Variation b d a (.pair c d)
  | tensorFirst {a b c d} (q : Wire c d) : Variation a b (.pair a c) (.pair b d)
  | tensorLast {a b c d} (p : Wire a b) : Variation c d (.pair a c) (.pair b d)

namespace Variation

def left : {u v a b : Shape Atom} → Variation u v a b → Template u v a b
  | _, _, _, _, .assocFirst q r => .seq (.seq .hole (.fixed q)) (.fixed r)
  | _, _, _, _, .assocMiddle p r => .seq (.seq (.fixed p) .hole) (.fixed r)
  | _, _, _, _, .assocLast p q => .seq (.seq (.fixed p) (.fixed q)) .hole
  | _, _, _, _, .leftId a _ => .seq (.fixed (.identity a)) .hole
  | _, _, _, _, .rightId _ b => .seq .hole (.fixed (.identity b))
  | _, _, _, _, .betaFstFirst (b := b) q => .seq (Template.pair .hole (.fixed q)) (.fixed (fst b _))
  | _, _, _, _, .betaFstLast (c := c) p => .seq (Template.pair (.fixed p) .hole) (.fixed (fst _ c))
  | _, _, _, _, .betaSndFirst (b := b) q => .seq (Template.pair .hole (.fixed q)) (.fixed (snd b _))
  | _, _, _, _, .betaSndLast (c := c) p => .seq (Template.pair (.fixed p) .hole) (.fixed (snd _ c))
  | _, _, _, _, .eta _ b c => Template.pair (.seq .hole (.fixed (fst b c))) (.seq .hole (.fixed (snd b c)))
  | _, _, _, _, .discard _ b => .seq .hole (.fixed (.discard b))
  | _, _, _, _, .forkFirst q r => .seq .hole (.fixed (fork q r))
  | _, _, _, _, .forkMiddle p r => .seq (.fixed p) (Template.pair .hole (.fixed r))
  | _, _, _, _, .forkLast p q => .seq (.fixed p) (Template.pair (.fixed q) .hole)
  | _, _, _, _, .tensorFirst q => .tensor .hole (.fixed q)
  | _, _, _, _, .tensorLast p => .tensor (.fixed p) .hole

def right : {u v a b : Shape Atom} → Variation u v a b → Template u v a b
  | _, _, _, _, .assocFirst q r => .seq .hole (.fixed (.seq q r))
  | _, _, _, _, .assocMiddle p r => .seq (.fixed p) (.seq .hole (.fixed r))
  | _, _, _, _, .assocLast p q => .seq (.fixed p) (.seq (.fixed q) .hole)
  | _, _, _, _, .leftId _ _ | _, _, _, _, .rightId _ _ => .hole
  | _, _, _, _, .betaFstFirst _ => .hole
  | _, _, _, _, .betaFstLast p => .fixed p
  | _, _, _, _, .betaSndFirst q => .fixed q
  | _, _, _, _, .betaSndLast _ => .hole
  | _, _, _, _, .eta _ _ _ => .hole
  | _, _, _, _, .discard a _ => .fixed (.discard a)
  | _, _, _, _, .forkFirst q r => Template.pair (.seq .hole (.fixed q)) (.seq .hole (.fixed r))
  | _, _, _, _, .forkMiddle p r => Template.pair (.seq (.fixed p) .hole) (.fixed (.seq p r))
  | _, _, _, _, .forkLast p q => Template.pair (.fixed (.seq p q)) (.seq (.fixed p) .hole)
  | _, _, _, _, .tensorFirst (a := a) q => Template.pair (.seq (.fixed (fst a _)) .hole) (.fixed (.seq (snd a _) q))
  | _, _, _, _, .tensorLast (c := c) p => Template.pair (.fixed (.seq (fst _ c) p)) (.seq (.fixed (snd _ c)) .hole)

def rootAt {u v a b : Shape Atom} (variation : Variation u v a b) (wire : Wire u v) :
    Root (variation.left.apply wire) (variation.right.apply wire) := by
  cases variation with
  | assocFirst q r => exact .assoc wire q r
  | assocMiddle p r => exact .assoc p wire r
  | assocLast p q => exact .assoc p q wire
  | leftId => exact .leftId wire
  | rightId => exact .rightId wire
  | betaFstFirst q => exact .betaFst wire q
  | betaFstLast p => exact .betaFst p wire
  | betaSndFirst q => exact .betaSnd wire q
  | betaSndLast p => exact .betaSnd p wire
  | eta => exact .eta wire
  | discard => exact .discardAfter wire
  | forkFirst q r => exact .forkAfter wire q r
  | forkMiddle p r => exact .forkAfter p wire r
  | forkLast p q => exact .forkAfter p q wire
  | tensorFirst q => exact .tensorExpand wire q
  | tensorLast p => exact .tensorExpand p wire

def code {u v a b : Shape Atom} (variation : Variation u v a b) : Fin 16 := by
  cases variation with
  | assocFirst => exact 0
  | assocMiddle => exact 1
  | assocLast => exact 2
  | leftId => exact 3
  | rightId => exact 4
  | betaFstFirst => exact 5
  | betaFstLast => exact 6
  | betaSndFirst => exact 7
  | betaSndLast => exact 8
  | eta => exact 9
  | discard => exact 10
  | forkFirst => exact 11
  | forkMiddle => exact 12
  | forkLast => exact 13
  | tensorFirst => exact 14
  | tensorLast => exact 15

theorem left_holes_le_two {u v a b : Shape Atom} (variation : Variation u v a b) : variation.left.holes ≤ 2 := by
  cases variation <;> decide_cbv

theorem right_holes_le_two {u v a b : Shape Atom} (variation : Variation u v a b) : variation.right.holes ≤ 2 := by
  cases variation <;> decide_cbv

end Variation
end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher
