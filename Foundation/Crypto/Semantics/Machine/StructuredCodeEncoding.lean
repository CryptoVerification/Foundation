import Foundation.Crypto.Semantics.Machine.ControlStorage
import Foundation.Crypto.Semantics.Machine.ListEncoding
import Foundation.Crypto.Semantics.ResourceGrowth

/-! A practical faithful code encoding, separate from the legacy unary
Encodable index of the entire program. Constant opcodes, tape/bit operands
and unary jump addresses are framed instruction by instruction. Its length
is linear in instruction count and the sum of address caps. Mathematical
encoding does not itself certify a native serialization implementation. -/
namespace Machine.StructuredCodeEncoding
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

private abbrev Fields := Nat × Bool × Bool × Nat × Nat × Nat

private def tapeBit : TapeId → Bool | .input => false | .output => true
private def bitTape : Bool → TapeId | false => .input | true => .output

private def pack : Instruction → Fields
  | .halt => (0, false, false, 0, 0, 0)
  | .moveLeft tape => (1, tapeBit tape, false, 0, 0, 0)
  | .moveRight tape => (2, tapeBit tape, false, 0, 0, 0)
  | .write tape bit => (3, tapeBit tape, bit, 0, 0, 0)
  | .erase tape => (4, tapeBit tape, false, 0, 0, 0)
  | .branch tape blankPc zeroPc onePc => (5, tapeBit tape, false, blankPc, zeroPc, onePc)
  | .jump pc => (6, false, false, pc, 0, 0)
  | .randomBit tape => (7, tapeBit tape, false, 0, 0, 0)

private def unpack (fields : Fields) : Instruction :=
  match fields.1 with
  | 0 => .halt
  | 1 => .moveLeft (bitTape fields.2.1)
  | 2 => .moveRight (bitTape fields.2.1)
  | 3 => .write (bitTape fields.2.1) fields.2.2.1
  | 4 => .erase (bitTape fields.2.1)
  | 5 => .branch (bitTape fields.2.1) fields.2.2.2.1 fields.2.2.2.2.1 fields.2.2.2.2.2
  | 6 => .jump fields.2.2.2.1
  | _ => .randomBit (bitTape fields.2.1)

private def fields : FiniteBitEncoding Fields :=
  ConfigurationEncoding.unary.prod (ConfigurationEncoding.bit.prod
    (ConfigurationEncoding.bit.prod (ConfigurationEncoding.unary.triple)))

def instruction : FiniteBitEncoding Instruction :=
  fields.retract pack unpack (by intro i; cases i <;> simp [pack, unpack, tapeBit, bitTape]; all_goals cases ‹TapeId› <;> rfl)

def program : FiniteBitEncoding Program := instruction.list

theorem instruction_length_le (i : Instruction) :
    (instruction.encode i).length ≤ 5 * i.addressCap + 23 := by
  cases i <;>
    simp [instruction, fields, pack, FiniteBitEncoding.triple, ConfigurationEncoding.unary,
      ConfigurationEncoding.bit, Instruction.addressCap]
  all_goals omega

/-- Variable code size and jump addresses both count, without indexing the whole list. -/
theorem program_length_le (code : Program) :
    (program.encode code).length ≤ 10 * code.addressCap + 48 * code.length + 1 := by
  induction code with
  | nil => decide
  | cons i rest ih =>
      have hi := instruction_length_le i
      change (instruction.list.encode (i :: rest)).length ≤ _
      rw [FiniteBitEncoding.list_encode_cons_length]
      change 2 * (instruction.encode i).length + 2 + (program.encode rest).length ≤ _
      simp only [Program.addressCap, List.length_cons]
      omega

def completeEncoding : FiniteBitEncoding (Program × Configuration) :=
  program.prod ConfigurationEncoding.configuration

theorem complete_length (code : Program) (state : Configuration) :
    (completeEncoding.encode (code, state)).length =
      2 * (program.encode code).length + 1 + (ConfigurationEncoding.configuration.encode state).length :=
  FiniteBitEncoding.prod_encode_length _ _ _ _

def bound (code : Program) (initialPc initialCells horizon : Nat) : Nat :=
  2 * (program.encode code).length + 2 * (initialPc + horizon * (code.addressCap + 1)) +
    18 * (initialCells + horizon) + 15

theorem bound_mono (code : Program) {pc nextPc cells nextCells time nextTime : Nat}
    (hPc : pc ≤ nextPc) (hCells : cells ≤ nextCells) (hTime : time ≤ nextTime) :
    bound code pc cells time ≤ bound code nextPc nextCells nextTime := by
  have hm := Nat.mul_le_mul_right (code.addressCap + 1) hTime
  unfold bound
  omega

theorem peak (code : Program) (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start state : Configuration) (hState : state ∈ (eval (stepPMF code) elapsed start).support) :
    (completeEncoding.encode (code, state)).length ≤ bound code start.pc start.tapeCells horizon := by
  have hPc := pc_prefix code horizon elapsed hElapsed start state hState
  have hCells := tapeCells_prefix code horizon elapsed hElapsed start state hState
  have hEncoding := ConfigurationEncoding.configuration_length_le state
  rw [complete_length]
  unfold bound
  omega

theorem boundary (code : Program) (stop : Configuration → Bool) (fuel : Nat)
    (start : Configuration) (result : Configuration × Nat)
    (hResult : result ∈ (runToBoundary (stepPMF code) stop fuel start).support) :
    (completeEncoding.encode (code, result.1)).length ≤ bound code start.pc start.tapeCells result.2 := by
  have hPc := ResourceGrowth.boundary_endpoint (stepPMF code) Configuration.pc
    (code.addressCap + 1) (pc_le_of_support code) stop fuel start result hResult
  have hCells := tapeCells_boundary code stop fuel start result hResult
  have hEncoding := ConfigurationEncoding.configuration_length_le result.1
  rw [complete_length]
  unfold bound
  omega

theorem bound_polynomial (code : Program) {pc cells time : Nat → Nat}
    (hPc : PolynomiallyBounded pc) (hCells : PolynomiallyBounded cells) (hTime : PolynomiallyBounded time) :
    PolynomiallyBounded (fun n => bound code (pc n) (cells n) (time n)) :=
  ((((PolynomiallyBounded.const (2 * (program.encode code).length)).add
    ((PolynomiallyBounded.const 2).mul (hPc.add (hTime.mul (PolynomiallyBounded.const (code.addressCap + 1)))))).add
      ((PolynomiallyBounded.const 18).mul (hCells.add hTime))).add (PolynomiallyBounded.const 15))

end Machine.StructuredCodeEncoding
