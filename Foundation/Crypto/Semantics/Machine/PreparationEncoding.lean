import Foundation.Crypto.Semantics.Machine.ConfigurationEncoding
import Foundation.Crypto.Semantics.Machine.ControllerStorage

/-! Faithful encoding of the operand preparation controller. The control
tag and temporary bits are retained alongside all three real tapes. No
buffer or private operand is reconstructed from a logical key value. -/
namespace Machine.PreparationEncoding
open Foundation.Probability

abbrev Fields := Nat × Option Bool × Option Bool × Tape × Tape × Tape

def fields := ConfigurationEncoding.unary.prod (ConfigurationEncoding.cell.prod
  (ConfigurationEncoding.cell.prod (ConfigurationEncoding.tape.prod
    (ConfigurationEncoding.tape.prod ConfigurationEncoding.tape))))

def view : PairPreparation.Control → Fields
  | .reading a b c => (0, none, none, a, b, c)
  | .checking x a b c => (1, some x, none, a, b, c)
  | .writingFirst x y a b c => (2, some x, some y, a, b, c)
  | .advancingFirst y a b c => (3, some y, none, a, b, c)
  | .writingSecond x a b c => (4, some x, none, a, b, c)
  | .advancingSecond a b c => (5, none, none, a, b, c)
  | .advancingKey a b c => (6, none, none, a, b, c)
  | .advancingMessage a b c => (7, none, none, a, b, c)
  | .checkingEnd a b c => (8, none, none, a, b, c)
  | .rewinding a b c => (9, none, none, a, b, c)
  | .ready a b c => (10, none, none, a, b, c)
  | .rejected a b c => (11, none, none, a, b, c)

def restore : Fields → Option PairPreparation.Control
  | (0, _, _, a, b, c) => some (.reading a b c)
  | (1, x, _, a, b, c) => x.map fun bit => .checking bit a b c
  | (2, x, y, a, b, c) => x.bind fun bit => y.map fun next => .writingFirst bit next a b c
  | (3, y, _, a, b, c) => y.map fun next => .advancingFirst next a b c
  | (4, x, _, a, b, c) => x.map fun bit => .writingSecond bit a b c
  | (5, _, _, a, b, c) => some (.advancingSecond a b c)
  | (6, _, _, a, b, c) => some (.advancingKey a b c)
  | (7, _, _, a, b, c) => some (.advancingMessage a b c)
  | (8, _, _, a, b, c) => some (.checkingEnd a b c)
  | (9, _, _, a, b, c) => some (.rewinding a b c)
  | (10, _, _, a, b, c) => some (.ready a b c)
  | (11, _, _, a, b, c) => some (.rejected a b c)
  | _ => none

def pair : FiniteBitEncoding PairPreparation.Control where
  encode := fun c => fields.encode (view c)
  decode := fun raw => (fields.decode raw).bind restore
  decode_encode := by intro c; cases c <;> simp [fields.decode_encode, view, restore]

private theorem field_length (tag : Nat) (x y : Option Bool) (a b c : Tape) :
    (fields.encode (tag, x, y, a, b, c)).length ≤ 2 * tag + 12 * (a.cells + b.cells + c.cells) + 28 := by
  have ha := ConfigurationEncoding.tape_length_le a
  have hb := ConfigurationEncoding.tape_length_le b
  have hc := ConfigurationEncoding.tape_length_le c
  have hx : (ConfigurationEncoding.cell.encode x).length = 2 := by cases x <;> rfl
  have hy : (ConfigurationEncoding.cell.encode y).length = 2 := by cases y <;> rfl
  simp only [fields, FiniteBitEncoding.prod_encode_length, ConfigurationEncoding.unary,
    List.length_replicate, hx, hy]
  omega

theorem pair_length_le (c : PairPreparation.Control) :
    (pair.encode c).length ≤ 12 * ControllerStorage.pairCells c + 50 := by
  have hf := field_length (view c).1 (view c).2.1 (view c).2.2.1
    (view c).2.2.2.1 (view c).2.2.2.2.1 (view c).2.2.2.2.2
  cases c <;> simp only [pair, view, ControllerStorage.pairCells] at hf ⊢ <;> omega

end Machine.PreparationEncoding
