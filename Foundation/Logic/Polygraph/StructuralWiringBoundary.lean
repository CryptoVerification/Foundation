import Foundation.Logic.Polygraph.StructuralWiringCompilation

/-! A verified limitation of the previous nine-root Cell language: no root
changes the number of unassoc gates. Hence even associator inverse cancellation
was missing there. The new complete compiled calculus certifies it. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Boundary

variable {Atom : Type}
def unassocCount : {first last : Shape Atom} → Wire first last → Nat
  | _, _, .seq first second => unassocCount first + unassocCount second
  | _, _, .tensor first second => unassocCount first + unassocCount second
  | _, _, .unassoc _ _ _ => 1
  | _, _, _ => 0

theorem old_cell_count {first last : Shape Atom} {one two : Wire first last} (cell : Cell one two) :
    unassocCount one = unassocCount two := by
  induction cell with
  | refl => rfl
  | symm cell ih => exact ih.symm
  | trans one two ihOne ihTwo => exact ihOne.trans ihTwo
  | seq one two ihOne ihTwo => exact congrArg₂ (· + ·) ihOne ihTwo
  | tensor one two ihOne ihTwo => exact congrArg₂ (· + ·) ihOne ihTwo
  | seqAssoc => simp only [unassocCount, Nat.add_assoc]
  | seqLeftUnit => simp only [unassocCount, Nat.zero_add]
  | seqRightUnit => simp only [unassocCount, Nat.add_zero]
  | tensorIdentity => rfl
  | interchange => simp only [unassocCount]; omega
  | copyAssoc => rfl
  | copySwap => rfl
  | copyDiscardLeft => rfl
  | copyDiscardRight => rfl

theorem old_inverse_missing (first second third : Shape Atom) :
    ¬ Nonempty (Cell (.seq (.assoc first second third) (.unassoc first second third))
      (.identity (.pair (.pair first second) third))) := by
  rintro ⟨cell⟩
  have impossible := old_cell_count cell
  change 0 + 1 = 0 at impossible
  omega

theorem inverse_evaluations_equal (first second third : Shape Atom) (family : Atom → Type)
    (value : (Shape.pair (.pair first second) third).Value family) :
    (Wire.seq (.assoc first second third) (.unassoc first second third)).eval family value = value := rfl

/-- A concrete compiled witness for one-atom inverse cancellation. The
normalizer constructs it from the finite primitive schemata. -/
def inverse_cell (first second third : Shape Unit) :
    FiniteWiring.Cell (Finite.compile (.seq (.assoc first second third) (.unassoc first second third)))
      (Finite.compile (.identity (.pair (.pair first second) third))) := by
  apply FiniteWiring.connect
  apply (FiniteWiring.complete _ _).mp
  apply (Finite.complete _ _).mpr
  intro A value
  exact inverse_evaluations_equal first second third (fun _ => A) value

end Foundation.Logic.Polygraph.StructuralTransport.Boundary
