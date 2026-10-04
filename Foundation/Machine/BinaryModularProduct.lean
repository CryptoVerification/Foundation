import Foundation.Machine.BinaryDoubleReduction
import Foundation.Machine.BinaryModularAddition

namespace Machine.BinaryModularProduct

/-- Numeric invariant for the bitwise modular-product loop. The recursive
suffix is evaluated first, so little-endian input is consumed from its most
significant bit. This is a specification for native code, not an arithmetic
instruction and not yet a complete multiplication program. -/
def step (modulus operand residue : Nat) (bit : Bool) : Nat :=
  ((2 * residue) % modulus + if bit then operand else 0) % modulus

def product (modulus operand : Nat) : List Bool → Nat
  | [] => 0
  | bit :: rest => step modulus operand (product modulus operand rest) bit

theorem product_value (modulus operand : Nat) (bits : List Bool) :
    product modulus operand bits = operand * Binary.value bits % modulus := by
  induction bits with
  | nil => simp [product, Binary.value]
  | cons bit rest ih =>
      calc
        product modulus operand (bit :: rest) =
            (2 * (operand * Binary.value rest) + if bit then operand else 0) % modulus := by
          simp only [product, step, ih, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
        _ = operand * Binary.value (bit :: rest) % modulus := by
          cases bit <;> simp only [Binary.value, Bool.toNat_false, Bool.toNat_true,
            Bool.false_eq_true, ↓reduceIte]
          all_goals congr 1; ring

theorem product_lt (modulus operand : Nat) (bits : List Bool) (hModulus : 0 < modulus) :
    product modulus operand bits < modulus := by
  rw [product_value]
  exact Nat.mod_lt _ hModulus

/-- Input layouts used in the operational certificates below. Preparing or
moving these layouts still requires charged bit-machine code in the complete
multiplier; these functions describe inputs and perform no free tape action. -/
def doubleInput (width residue modulus : Nat) : List (Bool × Bool) :=
  (Binary.encode width residue).zip (Binary.encode width modulus)

def addInput (width residue operand modulus : Nat) : List BinaryModularAddition.Column :=
  ((Binary.encode width residue).zip (Binary.encode width operand)).zip (Binary.encode width modulus)

private theorem doubleInput_length (width residue modulus : Nat) :
    (doubleInput width residue modulus).length = width := by
  simp [doubleInput]

private theorem doubleInput_fst (width residue modulus : Nat) :
    (doubleInput width residue modulus).map Prod.fst = Binary.encode width residue :=
  List.map_fst_zip (by simp)

private theorem doubleInput_snd (width residue modulus : Nat) :
    (doubleInput width residue modulus).map Prod.snd = Binary.encode width modulus :=
  List.map_snd_zip (by simp)

private theorem addInput_length (width residue operand modulus : Nat) :
    (addInput width residue operand modulus).length = width := by
  simp [addInput]

private theorem addInput_operands (width residue operand modulus : Nat) :
    BinaryModularAddition.operands (addInput width residue operand modulus) =
      (Binary.encode width residue).zip (Binary.encode width operand) :=
  List.map_fst_zip (by simp)

private theorem addInput_moduli (width residue operand modulus : Nat) :
    BinaryModularAddition.moduli (addInput width residue operand modulus) = Binary.encode width modulus :=
  List.map_snd_zip (by simp)

private theorem operands_fst (width residue operand : Nat) :
    ((Binary.encode width residue).zip (Binary.encode width operand)).map Prod.fst =
      Binary.encode width residue := List.map_fst_zip (by simp)

private theorem operands_snd (width residue operand : Nat) :
    ((Binary.encode width residue).zip (Binary.encode width operand)).map Prod.snd =
      Binary.encode width operand := List.map_snd_zip (by simp)

/-- Each arithmetic part of a product-loop iteration has a native execution
certificate: doubling, then adding the selected operand. Both execute the
previously proved fixed finite programs. This statement does not assume or
assert a free conversion between their input layouts, and consequently does
not yet assert an all-input stopping theorem for a full multiplier. -/
theorem step_kernels_correct (width modulus operand residue : Nat) (bit : Bool)
    (hResidue : residue < modulus) (hOperand : operand < modulus)
    (hModulus : modulus < 2 ^ width) (hRoom : 2 * modulus ≤ 2 ^ width) :
    evalWithin BinaryDoubleReduction.program
      (false :: BinaryComparison.interleave (doubleInput width residue modulus))
      (18 * width + 15) = PMF.pure (some (Binary.encode width (2 * residue % modulus))) ∧
    evalWithin BinaryModularAddition.program
      (BinaryModularAddition.interleave
        (addInput width (2 * residue % modulus) (if bit then operand else 0) modulus))
      (24 * width + 10) = PMF.pure (some (Binary.encode width (step modulus operand residue bit))) := by
  have hp : 0 < modulus := by omega
  have hResidueWidth : residue < 2 ^ width := hResidue.trans hModulus
  have hDoubled : 2 * residue % modulus < modulus := Nat.mod_lt _ hp
  have hDoubledWidth : 2 * residue % modulus < 2 ^ width := hDoubled.trans hModulus
  have hChosen : (if bit then operand else 0) < modulus := by cases bit <;> simp_all
  have hChosenWidth : (if bit then operand else 0) < 2 ^ width := hChosen.trans hModulus
  constructor
  · have h := BinaryDoubleReduction.eval_double_mod_encoded false (doubleInput width residue modulus)
      (by simpa only [doubleInput_fst, doubleInput_snd,
        Binary.value_encode hResidueWidth, Binary.value_encode hModulus] using hResidue)
      (by simp only [doubleInput_fst, doubleInput_length, Binary.value_encode hResidueWidth,
        Bool.toNat_false, Nat.add_zero]; omega)
    simpa only [doubleInput_length, doubleInput_fst, doubleInput_snd,
      Binary.value_encode hResidueWidth, Binary.value_encode hModulus,
      Bool.toNat_false, Nat.add_zero] using h
  · have h := BinaryModularAddition.eval_add_mod_encoded
      (addInput width (2 * residue % modulus) (if bit then operand else 0) modulus)
      (by simpa only [addInput_operands, addInput_moduli, operands_fst,
        Binary.value_encode hDoubledWidth, Binary.value_encode hModulus] using hDoubled)
      (by simpa only [addInput_operands, addInput_moduli, operands_snd,
        Binary.value_encode hChosenWidth, Binary.value_encode hModulus] using hChosen)
      (by simp only [addInput_operands, operands_fst, operands_snd, addInput_length,
        Binary.value_encode hDoubledWidth, Binary.value_encode hChosenWidth]; omega)
    simpa only [addInput_length, addInput_operands, operands_fst, operands_snd,
      addInput_moduli, Binary.value_encode hDoubledWidth, Binary.value_encode hChosenWidth,
      Binary.value_encode hModulus, step] using h

end Machine.BinaryModularProduct
