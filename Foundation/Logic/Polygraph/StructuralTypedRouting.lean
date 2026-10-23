import Foundation.Logic.Polygraph.StructuralTransport

/-! Typed symbolic inputs for arbitrary many-sorted product shapes. Routing
normal forms retain atom types and characterize equality for all value families.
This semantic characterization adds no rewrite or coherence generator. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.TypedRouting
variable {Atom : Type}

inductive Slot : Shape Atom → Atom → Type where
  | here (name : Atom) : Slot (.atom name) name
  | left {a b name} : Slot a name → Slot (.pair a b) name
  | right {a b name} : Slot b name → Slot (.pair a b) name
  deriving DecidableEq

def read {family : Atom → Type} : {shape : Shape Atom} → {name : Atom} →
    Slot shape name → shape.Value family → family name
  | _, _, .here _, value => value
  | _, _, .left slot, value => read slot value.1
  | _, _, .right slot, value => read slot value.2

def universal : (shape : Shape Atom) → shape.Value (Slot shape)
  | .atom name => .here name
  | .unit => PUnit.unit
  | .pair a b => (a.map (fun _ => Slot.left) (universal a), b.map (fun _ => Slot.right) (universal b))

theorem read_map {Old New : Atom → Type} (maps : ∀ name, Old name → New name)
    {shape : Shape Atom} {name} (slot : Slot shape name) (value : shape.Value Old) :
    read slot (shape.map maps value) = maps name (read slot value) := by
  induction slot with
  | here => rfl
  | left slot ih => exact ih value.1
  | right slot ih => exact ih value.2

theorem map_map {Old Middle New : Atom → Type} (first : ∀ name, Old name → Middle name)
    (second : ∀ name, Middle name → New name) (shape : Shape Atom) (value : shape.Value Old) :
    shape.map second (shape.map first value) = shape.map (fun name x => second name (first name x)) value := by
  induction shape with
  | atom => rfl
  | unit => rfl
  | pair a b one two => exact congrArg₂ Prod.mk (one value.1) (two value.2)

theorem map_identity {family : Atom → Type} (shape : Shape Atom) (value : shape.Value family) :
    shape.map (fun _ x => x) value = value := by
  induction shape with
  | atom => rfl
  | unit => cases value; rfl
  | pair a b one two => exact congrArg₂ Prod.mk (one value.1) (two value.2)

theorem read_universal {shape : Shape Atom} {name} (slot : Slot shape name) : read slot (universal shape) = slot := by
  induction slot with
  | here => rfl
  | left slot ih => simp only [universal, read, read_map, ih]
  | right slot ih => simp only [universal, read, read_map, ih]

theorem map_universal {family : Atom → Type} (shape : Shape Atom) (value : shape.Value family) :
    shape.map (fun _ slot => read slot value) (universal shape) = value := by
  induction shape with
  | atom => rfl
  | unit => cases value; rfl
  | pair a b one two =>
      simp only [universal, Shape.map, map_map, read]
      exact congrArg₂ Prod.mk (one value.1) (two value.2)

abbrev Layout (input output : Shape Atom) := output.Value (Slot input)

def normal {a b : Shape Atom} (wire : Wire a b) : Layout a b := wire.eval (Slot a) (universal a)

theorem normal_correct {family : Atom → Type} {a b : Shape Atom} (wire : Wire a b) (value : a.Value family) :
    b.map (fun _ slot => read slot value) (normal wire) = wire.eval family value := by
  rw [normal, Wire.naturality, map_universal]

theorem normal_complete {a b : Shape Atom} (first second : Wire a b) :
    normal first = normal second ↔ ∀ (family : Atom → Type) (value : a.Value family), first.eval family value = second.eval family value := by
  constructor
  · intro same family value
    rw [← normal_correct first value, ← normal_correct second value, same]
  · intro same
    exact same (Slot a) (universal a)

end Foundation.Logic.Polygraph.StructuralTransport.TypedRouting
