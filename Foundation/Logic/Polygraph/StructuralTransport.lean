import Foundation.Crypto.Semantics.Probability.Facts

/-! Typed structural circuits on already sampled values. All constructors
commute with deterministic changes of atomic representation, even on correlated
input laws. The local cell language has nine root schemata, but completeness
or higher coherence of that basis is NOT asserted. There is no reconstruction
rule or arbitrary semantic-equality generator. -/
namespace Foundation.Logic.Polygraph.StructuralTransport
open Foundation.Probability

inductive Shape (Atom : Type) where
  | atom : Atom → Shape Atom
  | unit : Shape Atom
  | pair : Shape Atom → Shape Atom → Shape Atom

variable {Atom : Type}

def Shape.Value (family : Atom → Type) : Shape Atom → Type
  | .atom name => family name
  | .unit => PUnit
  | .pair first second => first.Value family × second.Value family

def Shape.map {Old New : Atom → Type} (maps : ∀ atom, Old atom → New atom) :
    (shape : Shape Atom) → shape.Value Old → shape.Value New
  | .atom name, value => maps name value
  | .unit, _ => PUnit.unit
  | .pair first second, value => (first.map maps value.1, second.map maps value.2)

inductive Wire : Shape Atom → Shape Atom → Type where
  | identity (shape) : Wire shape shape
  | seq {first middle last} : Wire first middle → Wire middle last → Wire first last
  | tensor {first second first' second'} : Wire first second → Wire first' second' →
      Wire (.pair first first') (.pair second second')
  | copy (shape) : Wire shape (.pair shape shape)
  | discard (shape) : Wire shape .unit
  | swap (first second) : Wire (.pair first second) (.pair second first)
  | assoc (first second third) : Wire (.pair (.pair first second) third) (.pair first (.pair second third))
  | unassoc (first second third) : Wire (.pair first (.pair second third)) (.pair (.pair first second) third)
  | leftUnit (shape) : Wire (.pair .unit shape) shape
  | leftUnitInv (shape) : Wire shape (.pair .unit shape)
  | rightUnit (shape) : Wire (.pair shape .unit) shape
  | rightUnitInv (shape) : Wire shape (.pair shape .unit)

def Wire.eval (family : Atom → Type) : {first last : Shape Atom} →
    Wire first last → first.Value family → last.Value family
  | _, _, .identity _, value => value
  | _, _, .seq first second, value => second.eval family (first.eval family value)
  | _, _, .tensor first second, value => (first.eval family value.1, second.eval family value.2)
  | _, _, .copy _, value => (value, value)
  | _, _, .discard _, _ => PUnit.unit
  | _, _, .swap _ _, value => (value.2, value.1)
  | _, _, .assoc _ _ _, value => (value.1.1, (value.1.2, value.2))
  | _, _, .unassoc _ _ _, value => ((value.1, value.2.1), value.2.2)
  | _, _, .leftUnit _, value => value.2
  | _, _, .leftUnitInv _, value => (PUnit.unit, value)
  | _, _, .rightUnit _, value => value.1
  | _, _, .rightUnitInv _, value => (value, PUnit.unit)

theorem Wire.naturality {Old New : Atom → Type} (maps : ∀ atom, Old atom → New atom)
    {first last : Shape Atom} (wire : Wire first last) (value : first.Value Old) :
    last.map maps (wire.eval Old value) = wire.eval New (first.map maps value) := by
  induction wire with
  | identity => rfl
  | seq first second one two => simp only [eval, two, one]
  | tensor first second one two => exact congrArg₂ Prod.mk (one value.1) (two value.2)
  | copy => rfl
  | discard => rfl
  | swap => rfl
  | assoc => rfl
  | unassoc => rfl
  | leftUnit => rfl
  | leftUnitInv => rfl
  | rightUnit => rfl
  | rightUnitInv => rfl

theorem Wire.transport {Old New : Atom → Type} (maps : ∀ atom, Old atom → New atom)
    {first last : Shape Atom} (wire : Wire first last) (law : PMF (first.Value Old)) :
    (law.map (wire.eval Old)).map (last.map maps) = (law.map (first.map maps)).map (wire.eval New) := by
  simp only [PMF.map_comp]
  apply congrArg (fun function => law.map function)
  funext value
  exact wire.naturality maps value

/-- An arbitrary earlier context stays in the joint law. Tensor evaluates
both components of each sampled input; it does not resample independent runs. -/
theorem Wire.transport_joint {Old New : Atom → Type} {Context : Type}
    (maps : ∀ atom, Old atom → New atom) {first last : Shape Atom} (wire : Wire first last)
    (law : PMF (Context × first.Value Old)) :
    (law.map (fun value => (value.1, wire.eval Old value.2))).map (fun value => (value.1, last.map maps value.2)) =
      (law.map (fun value => (value.1, first.map maps value.2))).map (fun value => (value.1, wire.eval New value.2)) := by
  simp only [PMF.map_comp, Function.comp_def]
  apply congrArg (fun function => law.map function)
  funext value
  exact congrArg (fun output => (value.1, output)) (wire.naturality maps value.2)

inductive Cell : {first last : Shape Atom} → Wire first last → Wire first last → Type where
  | refl {first last} (wire : Wire first last) : Cell wire wire
  | symm {first last} {one two : Wire first last} : Cell one two → Cell two one
  | trans {first last} {one two three : Wire first last} : Cell one two → Cell two three → Cell one three
  | seq {first middle last} {one one' : Wire first middle} {two two' : Wire middle last} :
      Cell one one' → Cell two two' → Cell (.seq one two) (.seq one' two')
  | tensor {first last first' last'} {one one' : Wire first last} {two two' : Wire first' last'} :
      Cell one one' → Cell two two' → Cell (.tensor one two) (.tensor one' two')
  | seqAssoc {a b c d} (one : Wire a b) (two : Wire b c) (three : Wire c d) :
      Cell (.seq (.seq one two) three) (.seq one (.seq two three))
  | seqLeftUnit {a b} (wire : Wire a b) : Cell (.seq (.identity a) wire) wire
  | seqRightUnit {a b} (wire : Wire a b) : Cell (.seq wire (.identity b)) wire
  | tensorIdentity (first second) : Cell (.tensor (.identity first) (.identity second)) (.identity (.pair first second))
  | interchange {a b c a' b' c'} (one : Wire a b) (two : Wire b c) (one' : Wire a' b') (two' : Wire b' c') :
      Cell (.seq (.tensor one one') (.tensor two two')) (.tensor (.seq one two) (.seq one' two'))
  | copyAssoc (shape) :
      Cell (.seq (.seq (.copy shape) (.tensor (.copy shape) (.identity shape))) (.assoc shape shape shape))
        (.seq (.copy shape) (.tensor (.identity shape) (.copy shape)))
  | copySwap (shape) : Cell (.seq (.copy shape) (.swap shape shape)) (.copy shape)
  | copyDiscardLeft (shape) :
      Cell (.seq (.seq (.copy shape) (.tensor (.discard shape) (.identity shape))) (.leftUnit shape)) (.identity shape)
  | copyDiscardRight (shape) :
      Cell (.seq (.seq (.copy shape) (.tensor (.identity shape) (.discard shape))) (.rightUnit shape)) (.identity shape)

theorem Cell.sound {first last : Shape Atom} {one two : Wire first last}
    (cell : Cell one two) (family : Atom → Type) (value : first.Value family) :
    one.eval family value = two.eval family value := by
  induction cell with
  | refl => rfl
  | symm cell ih => exact (ih value).symm
  | trans one two ihOne ihTwo => exact (ihOne value).trans (ihTwo value)
  | seq one two ihOne ihTwo => simp only [Wire.eval, ihOne, ihTwo]
  | tensor one two ihOne ihTwo => exact congrArg₂ Prod.mk (ihOne value.1) (ihTwo value.2)
  | seqAssoc => rfl
  | seqLeftUnit => rfl
  | seqRightUnit => rfl
  | tensorIdentity => rfl
  | interchange => rfl
  | copyAssoc => rfl
  | copySwap => rfl
  | copyDiscardLeft => rfl
  | copyDiscardRight => rfl

theorem Cell.distribution {first last : Shape Atom} {one two : Wire first last}
    (cell : Cell one two) (family : Atom → Type) (law : PMF (first.Value family)) :
    law.map (one.eval family) = law.map (two.eval family) := by
  exact congrArg (fun function => law.map function) (funext (cell.sound family))

end Foundation.Logic.Polygraph.StructuralTransport
