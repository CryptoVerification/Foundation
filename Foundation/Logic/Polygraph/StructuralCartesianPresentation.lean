import Foundation.Logic.Polygraph.StructuralTypedRouting

/-! An explicit eighteen-form cartesian equation presentation on the existing
pure Wire syntax. Projections and pairing are fixed structural macros. No
whole-normalization or arbitrary semantic-equality equation is a root. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian
variable {Atom : Type}

def fst (a b : Shape Atom) : Wire (.pair a b) a := .seq (.tensor (.identity a) (.discard b)) (.rightUnit a)
def snd (a b : Shape Atom) : Wire (.pair a b) b := .seq (.tensor (.discard a) (.identity b)) (.leftUnit b)
def fork {a b c : Shape Atom} (p : Wire a b) (q : Wire a c) : Wire a (.pair b c) := .seq (.copy a) (.tensor p q)

inductive Root : {a b : Shape Atom} → Wire a b → Wire a b → Type where
  | assoc {a b c d} (p : Wire a b) (q : Wire b c) (r : Wire c d) : Root (.seq (.seq p q) r) (.seq p (.seq q r))
  | leftId {a b} (p : Wire a b) : Root (.seq (.identity a) p) p
  | rightId {a b} (p : Wire a b) : Root (.seq p (.identity b)) p
  | betaFst {a b c} (p : Wire a b) (q : Wire a c) : Root (.seq (fork p q) (fst b c)) p
  | betaSnd {a b c} (p : Wire a b) (q : Wire a c) : Root (.seq (fork p q) (snd b c)) q
  | eta {a b c} (p : Wire a (.pair b c)) : Root (fork (.seq p (fst b c)) (.seq p (snd b c))) p
  | discardAfter {a b} (p : Wire a b) : Root (.seq p (.discard b)) (.discard a)
  | forkAfter {a b c d} (p : Wire a b) (q : Wire b c) (r : Wire b d) :
      Root (.seq p (fork q r)) (fork (.seq p q) (.seq p r))
  | tensorExpand {a b c d} (p : Wire a b) (q : Wire c d) :
      Root (.tensor p q) (fork (.seq (fst a c) p) (.seq (snd a c) q))
  | copyExpand (a : Shape Atom) : Root (.copy a) (fork (.identity a) (.identity a))
  | swapExpand (a b : Shape Atom) : Root (.swap a b) (fork (snd a b) (fst a b))
  | assocExpand (a b c : Shape Atom) : Root (.assoc a b c)
      (fork (.seq (fst (.pair a b) c) (fst a b)) (fork (.seq (fst (.pair a b) c) (snd a b)) (snd (.pair a b) c)))
  | unassocExpand (a b c : Shape Atom) : Root (.unassoc a b c)
      (fork (fork (fst a (.pair b c)) (.seq (snd a (.pair b c)) (fst b c))) (.seq (snd a (.pair b c)) (snd b c)))
  | leftUnitExpand (a : Shape Atom) : Root (.leftUnit a) (snd .unit a)
  | rightUnitExpand (a : Shape Atom) : Root (.rightUnit a) (fst a .unit)
  | leftUnitInvExpand (a : Shape Atom) : Root (.leftUnitInv a) (fork (.discard a) (.identity a))
  | rightUnitInvExpand (a : Shape Atom) : Root (.rightUnitInv a) (fork (.identity a) (.discard a))
  | unitIdentity : Root (.identity (.unit : Shape Atom)) (.discard .unit)

def Root.code {a b : Shape Atom} {p q : Wire a b} (root : Root p q) : Fin 18 := by
  cases root with
  | assoc => exact 0
  | leftId => exact 1
  | rightId => exact 2
  | betaFst => exact 3
  | betaSnd => exact 4
  | eta => exact 5
  | discardAfter => exact 6
  | forkAfter => exact 7
  | tensorExpand => exact 8
  | copyExpand => exact 9
  | swapExpand => exact 10
  | assocExpand => exact 11
  | unassocExpand => exact 12
  | leftUnitExpand => exact 13
  | rightUnitExpand => exact 14
  | leftUnitInvExpand => exact 15
  | rightUnitInvExpand => exact 16
  | unitIdentity => exact 17

theorem Root.sound {a b} {p q : Wire (Atom := Atom) a b} (root : Root p q)
    (family : Atom → Type) (value : a.Value family) : p.eval family value = q.eval family value := by
  cases root <;> rfl

inductive Cell : {a b : Shape Atom} → Wire a b → Wire a b → Type where
  | refl {a b} (p : Wire a b) : Cell p p
  | symm {a b} {p q : Wire a b} : Cell p q → Cell q p
  | trans {a b} {p q r : Wire a b} : Cell p q → Cell q r → Cell p r
  | seq {a b c} {p p' : Wire a b} {q q' : Wire b c} : Cell p p' → Cell q q' → Cell (.seq p q) (.seq p' q')
  | tensor {a b c d} {p p' : Wire a b} {q q' : Wire c d} : Cell p p' → Cell q q' → Cell (.tensor p q) (.tensor p' q')
  | root {a b} {p q : Wire a b} : Root p q → Cell p q

def Cell.fork {a b c} {p p' : Wire (Atom := Atom) a b} {q q' : Wire a c} (first : Cell p p') (second : Cell q q') :
    Cell (fork p q) (fork p' q') := .seq (.refl _) (.tensor first second)

theorem Cell.sound {a b} {p q : Wire (Atom := Atom) a b} (cell : Cell p q)
    (family : Atom → Type) (value : a.Value family) : p.eval family value = q.eval family value := by
  induction cell with
  | refl => rfl
  | symm child ih => exact (ih value).symm
  | trans first second one two => exact (one value).trans (two value)
  | seq first second one two =>
      simp only [Wire.eval, one value, two]
  | tensor first second one two => exact congrArg₂ Prod.mk (one value.1) (two value.2)
  | root root => exact root.sound family value

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian
