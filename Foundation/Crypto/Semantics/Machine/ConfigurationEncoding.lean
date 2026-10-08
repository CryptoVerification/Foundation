import Foundation.Crypto.Semantics.Machine.Encoding
import Foundation.Crypto.Semantics.Machine.Storage

/-! Faithful explicit bit encodings of complete native configurations.
Unary addresses give a conservative size bound; encoding/decoding are
mathematical representations, not new unit-cost machine instructions. -/
namespace Machine.ConfigurationEncoding
open Foundation.Probability

def bit : FiniteBitEncoding Bool where
  encode := fun b => [b]
  decode := fun raw => match raw with | [b] => some b | _ => none
  decode_encode := by intro b; rfl

def unary : FiniteBitEncoding Nat where
  encode := fun n => List.replicate n true
  decode := fun raw => if raw = List.replicate raw.length true then some raw.length else none
  decode_encode := by intro n; simp

def cell : FiniteBitEncoding (Option Bool) where
  encode := fun value => match value with
    | none => [false, false]
    | some b => [true, b]
  decode := fun raw => match raw with
    | [false, false] => some none
    | [true, b] => some (some b)
    | _ => none
  decode_encode := by intro value; cases value <;> rfl

def encodeCells : List (Option Bool) → List Bool
  | [] => [false]
  | c :: rest => true :: cell.encode c ++ encodeCells rest

def decodeCells : List Bool → Option (List (Option Bool))
  | [false] => some []
  | true :: a :: b :: rest => do
      let c ← cell.decode [a, b]
      let tail ← decodeCells rest
      pure (c :: tail)
  | _ => none

theorem decodeCells_encodeCells (cells : List (Option Bool)) :
    decodeCells (encodeCells cells) = some cells := by
  induction cells with
  | nil => rfl
  | cons c rest ih => cases c <;> simp [encodeCells, cell, decodeCells, ih]

theorem encodeCells_length (cells : List (Option Bool)) :
    (encodeCells cells).length = 3 * cells.length + 1 := by
  induction cells with
  | nil => rfl
  | cons c rest ih => cases c <;> simp [encodeCells, cell, ih] <;> omega

def cells : FiniteBitEncoding (List (Option Bool)) :=
  ⟨encodeCells, decodeCells, decodeCells_encodeCells⟩

def tapeFields := cells.prod (cell.prod cells)

def tape : FiniteBitEncoding Tape where
  encode := fun t => tapeFields.encode (t.left, t.current, t.right)
  decode := fun raw => (tapeFields.decode raw).map fun fields =>
    { left := fields.1, current := fields.2.1, right := fields.2.2 }
  decode_encode := by intro t; simp [tapeFields.decode_encode]

theorem tape_length (t : Tape) :
    (tape.encode t).length = 6 * t.left.length + 3 * t.right.length + 9 := by
  have hc : (cell.encode t.current).length = 2 := by cases t.current <;> rfl
  simp only [tape, tapeFields, FiniteBitEncoding.prod_encode_length, cells, encodeCells_length, hc]
  omega

theorem tape_length_le (t : Tape) : (tape.encode t).length ≤ 6 * t.cells + 3 := by
  rw [tape_length]
  unfold Tape.cells
  omega

def configurationFields := unary.prod (bit.prod (tape.prod tape))

def configuration : FiniteBitEncoding Configuration where
  encode := fun c => configurationFields.encode (c.pc, c.halted, c.inputTape, c.outputTape)
  decode := fun raw => (configurationFields.decode raw).map fun fields =>
    { pc := fields.1, halted := fields.2.1, inputTape := fields.2.2.1, outputTape := fields.2.2.2 }
  decode_encode := by intro c; simp [configurationFields.decode_encode]

theorem configuration_length (c : Configuration) :
    (configuration.encode c).length = 2 * c.pc +
      2 * (tape.encode c.inputTape).length + (tape.encode c.outputTape).length + 5 := by
  simp [configuration, configurationFields, FiniteBitEncoding.prod_encode_length, unary, bit]
  omega

theorem configuration_length_le (c : Configuration) :
    (configuration.encode c).length ≤ 2 * c.pc + 18 * c.tapeCells + 14 := by
  have hi := tape_length_le c.inputTape
  have ho := tape_length_le c.outputTape
  rw [configuration_length]
  unfold Configuration.tapeCells
  omega

end Machine.ConfigurationEncoding
