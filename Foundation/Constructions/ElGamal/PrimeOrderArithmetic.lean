import Foundation.Constructions.ElGamal.PrimeOrderRepresentation
import Foundation.Machine.BinaryProductExternalWidth
import Foundation.Machine.BinaryPowerExternalWidth
import Foundation.Machine.FramedInstanceCopy
import Foundation.Machine.PrimeModulusProjection
import Foundation.Machine.FramedModulusCopy
import Foundation.Machine.FramedFirstOperandCopy
import Foundation.Machine.FramedSecondOperandCopy
import Foundation.Machine.BinaryColumnSlotFill
import Foundation.Machine.FramedProductColumns
import Foundation.Machine.FramedProductMultiply
import Foundation.Machine.FramedProductSafeMultiply
import Foundation.Constructions.ElGamal.MachinePrimitives

namespace ElGamal.PrimeOrderRepresentation

/-- The three physical slot-writing passes produce exactly the raw input
layout of the existing modular multiplication code. This layout identity
does not itself install any intermediate tape as a machine action. -/
theorem fullSlots_numberColumns (width modulus first second : Nat) :
    Machine.BinaryColumnSlotFill.fullSlots
      (Machine.Binary.encode width first)
      (Machine.Binary.encode width second)
      (Machine.Binary.encode width modulus) =
    Machine.BinaryModularAddition.interleave
      (Machine.BinaryProductExternalWidth.numberColumns
        width modulus first second) := by
  rfl

/-- The framed finite program reaches the raw multiplication columns on its
actual output tape. This is the parser/layout stage; the arithmetic call
and the whole-program stopping certificate remain separate. -/
theorem framedProductColumns_run (n : Nat) (x : Domain n)
    (a b : (embed n x).params.Element) :
    let C := x.down
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++
      Machine.frame ((elementCode n x).encode a) ++
      Machine.frame ((elementCode n x).encode b)
    ∃ target used,
      Machine.RunsFor Machine.FramedProductColumns.program
        (Machine.Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.outputBits =
        Machine.BinaryModularAddition.interleave
          (Machine.BinaryProductExternalWidth.numberColumns
            (n + 3) C.modulus a.val.val.val b.val.val.val) := by
  dsimp only
  let C := x.down
  let p := Machine.Binary.encode (n + 3) C.modulus
  let q := Machine.Binary.encode (n + 3) C.scalarOrder
  let g := Machine.Binary.encode (n + 3) C.generator.val.val
  let aBits := Machine.Binary.encode (n + 3) a.val.val.val
  let bBits := Machine.Binary.encode (n + 3) b.val.val.val
  obtain ⟨target, used, run, hHalt, _, hOutput⟩ :=
    Machine.FramedProductColumns.runs_valid n p q g aBits bBits []
      (Machine.Binary.encode_length _ _)
      (by simp [p, q]) (by simp [p, g])
      (by simp [p, aBits]) (by simp [p, bBits])
  refine ⟨target, used, ?_, hHalt, ?_⟩
  · simpa [C, p, q, g, aBits, bBits,
      PrimeOrderRepresentation.instanceCode,
      PrimeOrderParameters.instanceCode,
      PrimeOrderRepresentation.elementCode,
      PrimeOrderParameters.elementCode,
      List.append_assoc] using run
  · have hBits := hOutput.bits
    have hLayout : target.outputBits =
        Machine.BinaryColumnSlotFill.fullSlots aBits bBits p := by
      simpa [Machine.Configuration.outputBits, Machine.Tape.bits,
        List.reverse_cons, List.map_reverse, List.filterMap_append] using hBits
    rw [hLayout]
    exact fullSlots_numberColumns (n + 3) C.modulus a.val.val.val b.val.val.val

/-- The finite parser copies the actual parameter encoding before the
arithmetic wrapper selects its modulus field. This is only the first native
stage of the framed multiplier. -/
theorem framedInstance_eval (n : Nat) (x : Domain n) (rest : List Bool) :
    let code := (instanceCode n).encode x
    let raw := Machine.encodeSecurityParameter n ++ Machine.frame code ++ rest
    Machine.evalWithin Machine.FramedInstanceCopy.program raw
      (Machine.FramedInstanceCopy.budget raw.length) = PMF.pure (some code) := by
  exact Machine.FramedInstanceCopy.eval_valid n ((instanceCode n).encode x) rest

/-- After the instance has been copied by finite code, the projector reads
its modulus field from the physical copied-tape layout. -/
theorem framedModulus_projection_eval (n : Nat) (x : Domain n)
    (rest : List Bool) :
    let width := n + 3
    let C := x.down
    let p := Machine.Binary.encode width C.modulus
    let q := Machine.Binary.encode width C.scalarOrder
    let g := Machine.Binary.encode width C.generator.val.val
    let code := p ++ q ++ g
    let input : Machine.Tape :=
      { Machine.Tape.ofBits rest with
        left := code.reverse.map some ++ some false ::
          List.replicate code.length (some true) ++
            some false :: List.replicate n (some true) }
    let start : Machine.Configuration :=
      { inputTape := input,
        outputTape := { left := code.reverse.map some ++ [none] } }
    (Machine.evalConfigWithin Machine.PrimeModulusProjection.program start
      (Machine.PrimeModulusProjection.budget code.length)).map
        (fun c => if c.halted then some c.outputBits else none) =
      PMF.pure (some p) := by
  dsimp only
  exact Machine.PrimeModulusProjection.eval_valid _ _ _ _ (n + 3)
    (List.replicate n (some true))
    (Machine.Binary.encode_length _ _)
    (Machine.Binary.encode_length _ _)
    (Machine.Binary.encode_length _ _)
    rfl

/-- The framed instance copier and modulus projector run as one finite
instruction list on the actual encoded prime-order instance. A subsequent
nonempty element frame has its leading `true` under the input head. -/
theorem framedModulus_run (n : Nat) (x : Domain n) (rest : List Bool) :
    let code := (instanceCode n).encode x
    let raw := Machine.encodeSecurityParameter n ++ Machine.frame code ++ rest
    ∃ target used, used ≤ Machine.FramedModulusCopy.budget raw.length ∧
      Machine.RunsFor Machine.FramedModulusCopy.program
        (Machine.Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.outputBits = Machine.Binary.encode (n + 3) x.down.modulus ∧
      target.inputTape.current = some true := by
  dsimp only
  let C := x.down
  let p := Machine.Binary.encode (n + 3) C.modulus
  let q := Machine.Binary.encode (n + 3) C.scalarOrder
  let g := Machine.Binary.encode (n + 3) C.generator.val.val
  have hRun := Machine.FramedModulusCopy.runs_valid n (n + 3) p q g rest
    (Machine.Binary.encode_length _ _)
    (Machine.Binary.encode_length _ _)
    (Machine.Binary.encode_length _ _)
  obtain ⟨target, used, hUsed, run, hHalt, _, _, hBits, hHead⟩ := hRun
  refine ⟨target, used, ?_, ?_, hHalt, ?_, hHead⟩
  · simpa [PrimeOrderRepresentation.instanceCode,
      PrimeOrderParameters.instanceCode, C, p, q, g] using hUsed
  · simpa [PrimeOrderRepresentation.instanceCode,
      PrimeOrderParameters.instanceCode, C, p, q, g] using run
  · simpa [C, p] using hBits

/-- The composed finite parser evaluates to the encoded modulus on the
actual prime-order instance frame. Its all-input polynomial stopping is
`FramedModulusCopy.polynomialTime`; operand alignment remains separate. -/
theorem framedModulus_eval (n : Nat) (x : Domain n) (rest : List Bool) :
    let code := (instanceCode n).encode x
    let raw := Machine.encodeSecurityParameter n ++ Machine.frame code ++ rest
    Machine.evalWithin Machine.FramedModulusCopy.program raw
      (Machine.FramedModulusCopy.budget raw.length) =
      PMF.pure (some (Machine.Binary.encode (n + 3) x.down.modulus)) := by
  dsimp only
  let C := x.down
  let p := Machine.Binary.encode (n + 3) C.modulus
  let q := Machine.Binary.encode (n + 3) C.scalarOrder
  let g := Machine.Binary.encode (n + 3) C.generator.val.val
  have hEval := Machine.FramedModulusCopy.eval_valid n (n + 3) p q g rest
    (Machine.Binary.encode_length _ _)
    (Machine.Binary.encode_length _ _)
    (Machine.Binary.encode_length _ _)
  simpa [PrimeOrderRepresentation.instanceCode,
    PrimeOrderParameters.instanceCode, C, p, q, g]
    using hEval

set_option maxHeartbeats 1000000 in
/-- A separate finite parser extracts the first encoded operand and leaves
the input head at the second operand frame. Its all-input stopping theorem is
`FramedFirstOperandCopy.polynomialTime`. This does not yet interleave the two
operands with the modulus for the raw arithmetic program. -/
theorem framedFirstOperand_eval (n : Nat) (x : Domain n)
    (a b : (embed n x).params.Element) :
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++
      Machine.frame ((elementCode n x).encode a) ++
      Machine.frame ((elementCode n x).encode b)
    Machine.evalWithin Machine.FramedFirstOperandCopy.program raw
      (Machine.FramedFirstOperandCopy.budget raw.length) =
      PMF.pure (some ((elementCode n x).encode a)) := by
  simpa only [List.append_assoc, List.append_nil] using
    (Machine.FramedFirstOperandCopy.eval_valid n
      ((instanceCode n).encode x) ((elementCode n x).encode a)
      ((elementCode n x).encode b) [])

/-- A distinct finite parser reads the second element frame on the same
physical request tape after erasing the first payload's scratch copy. This
does not yet assemble the interleaved raw multiplication input. -/
theorem framedSecondOperand_eval (n : Nat) (x : Domain n)
    (a b : (embed n x).params.Element) :
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++
      Machine.frame ((elementCode n x).encode a) ++
      Machine.frame ((elementCode n x).encode b)
    Machine.evalWithin Machine.FramedSecondOperandCopy.program raw
      (Machine.FramedSecondOperandCopy.budget raw.length) =
      PMF.pure (some ((elementCode n x).encode b)) := by
  simpa only [List.append_assoc, List.append_nil] using
    (Machine.FramedSecondOperandCopy.eval_valid n
      ((instanceCode n).encode x) ((elementCode n x).encode a)
      ((elementCode n x).encode b) [])

/-- The native finite-bit multiplier agrees with the prime-order group's
encoded multiplication when its input is the raw interleaved residue triple. -/
theorem rawMultiply_correct (n : Nat) (x : Domain n)
    (a b : (embed n x).params.Element) :
    let C := x.down
    let raw := Machine.BinaryModularAddition.interleave
      (Machine.BinaryProductExternalWidth.numberColumns (n + 3)
        C.modulus a.val.val.val b.val.val.val)
    Machine.evalWithin Machine.BinaryProductExternalWidth.program raw
      (Machine.BinaryProductExternalWidth.budget raw.length) =
      PMF.pure (some ((elementCode n x).encode ((embed n x).params.mul a b))) := by
  dsimp only
  let C := x.down
  haveI : Fact C.modulus.Prime := ⟨C.modulus_prime⟩
  haveI : NeZero C.modulus := ⟨C.modulus_prime.ne_zero⟩
  change C.parameters.Element at a b
  have ha : a.val.val.val < C.modulus := ZMod.val_lt _
  have hb : b.val.val.val < C.modulus := ZMod.val_lt _
  have hNative := Machine.BinaryProductExternalWidth.eval_numbers
    (n + 3) C.modulus a.val.val.val b.val.val.val ha hb C.modulus_lt
  change Machine.evalWithin Machine.BinaryProductExternalWidth.program
    (Machine.BinaryModularAddition.interleave
      (Machine.BinaryProductExternalWidth.numberColumns (n + 3)
        C.modulus a.val.val.val b.val.val.val))
    (Machine.BinaryProductExternalWidth.budget
      (Machine.BinaryModularAddition.interleave
        (Machine.BinaryProductExternalWidth.numberColumns (n + 3)
          C.modulus a.val.val.val b.val.val.val)).length) =
    PMF.pure (some (C.elementCode.encode (C.parameters.mul a b)))
  rw [C.elementCode_mul]
  exact hNative

/-- The complete framed request has an actual finite machine trace whose
output is the encoded group product. This theorem concerns valid requests;
the separate all-input polynomial stopping certificate is still required for
the simulator primitive interface. -/
theorem framedMultiply_run (n : Nat) (x : Domain n)
    (a b : (embed n x).params.Element) :
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++
      Machine.frame ((elementCode n x).encode a) ++
      Machine.frame ((elementCode n x).encode b)
    ∃ target used,
      Machine.RunsFor Machine.FramedProductMultiply.program
        (Machine.Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.outputBits =
        (elementCode n x).encode ((embed n x).params.mul a b) := by
  dsimp only
  let C := x.down
  haveI : Fact C.modulus.Prime := ⟨C.modulus_prime⟩
  haveI : NeZero C.modulus := ⟨C.modulus_prime.ne_zero⟩
  change C.parameters.Element at a b
  have ha : a.val.val.val < C.modulus := ZMod.val_lt _
  have hb : b.val.val.val < C.modulus := ZMod.val_lt _
  have haWidth : a.val.val.val < 2 ^ (n + 3) := ha.trans C.modulus_lt
  have hbWidth : b.val.val.val < 2 ^ (n + 3) := hb.trans C.modulus_lt
  let p := Machine.Binary.encode (n + 3) C.modulus
  let q := Machine.Binary.encode (n + 3) C.scalarOrder
  let g := Machine.Binary.encode (n + 3) C.generator.val.val
  let aBits := Machine.Binary.encode (n + 3) a.val.val.val
  let bBits := Machine.Binary.encode (n + 3) b.val.val.val
  have hOperand : Machine.Binary.value aBits < Machine.Binary.value p := by
    simpa [aBits, p, Machine.Binary.value_encode haWidth, C.modulus_lt] using ha
  have hWidth : Machine.Binary.value p < 2 ^ p.length := by
    simpa [p, Machine.Binary.value_encode C.modulus_lt] using C.modulus_lt
  obtain ⟨target, used, run, hHalt, hOutput⟩ :=
    Machine.FramedProductMultiply.runs_valid n p q g aBits bBits
      (Machine.Binary.encode_length _ _)
      (by simp [p, q]) (by simp [p, g])
      (by simp [p, aBits]) (by simp [p, bBits])
      hOperand hWidth
  refine ⟨target, used, ?_, hHalt, ?_⟩
  · simpa [C, p, q, g, aBits, bBits,
      PrimeOrderRepresentation.instanceCode,
      PrimeOrderParameters.instanceCode,
      PrimeOrderRepresentation.elementCode,
      PrimeOrderParameters.elementCode,
      List.append_assoc] using run
  · have hNumeric : target.outputBits = Machine.Binary.encode (n + 3)
        (a.val.val.val * b.val.val.val % C.modulus) := by
      simpa [p, aBits, bBits,
        Machine.Binary.value_encode haWidth,
        Machine.Binary.value_encode hbWidth,
        Machine.Binary.value_encode C.modulus_lt] using hOutput
    change target.outputBits = C.elementCode.encode (C.parameters.mul a b)
    rw [C.elementCode_mul]
    exact hNumeric

/-- At the witnessed stopping time, the framed native multiplier evaluates
to the exact encoded group product. A uniform polynomial budget for all raw
inputs is still needed before this can populate `multiply_correct`. -/
theorem framedMultiply_eval_at_used (n : Nat) (x : Domain n)
    (a b : (embed n x).params.Element) :
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++
      Machine.frame ((elementCode n x).encode a) ++
      Machine.frame ((elementCode n x).encode b)
    ∃ used,
      Machine.evalWithin Machine.FramedProductMultiply.program raw used =
        PMF.pure (some ((elementCode n x).encode ((embed n x).params.mul a b))) := by
  dsimp only
  obtain ⟨target, used, run, hHalt, hOutput⟩ := framedMultiply_run n x a b
  refine ⟨used, ?_⟩
  unfold Machine.evalWithin
  rw [run.evalConfigWithin_eq_pure_of_no_randomBit
      Machine.FramedProductMultiply.no_randomBit, PMF.pure_map]
  simp [hHalt, hOutput]

/-- The complete framed native multiplier computes the group product at its
explicit valid-request budget. This does not assert all-input stopping. -/
theorem framedMultiply_eval_at_budget (n : Nat) (x : Domain n)
    (a b : (embed n x).params.Element) :
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++
      Machine.frame ((elementCode n x).encode a) ++
      Machine.frame ((elementCode n x).encode b)
    let C := x.down
    let p := Machine.Binary.encode (n + 3) C.modulus
    let q := Machine.Binary.encode (n + 3) C.scalarOrder
    let g := Machine.Binary.encode (n + 3) C.generator.val.val
    let aBits := Machine.Binary.encode (n + 3) a.val.val.val
    let bBits := Machine.Binary.encode (n + 3) b.val.val.val
    Machine.evalWithin Machine.FramedProductMultiply.program raw
      (Machine.FramedProductMultiply.validBudget n p q g aBits bBits) =
        PMF.pure (some ((elementCode n x).encode ((embed n x).params.mul a b))) := by
  dsimp only
  let C := x.down
  haveI : Fact C.modulus.Prime := ⟨C.modulus_prime⟩
  haveI : NeZero C.modulus := ⟨C.modulus_prime.ne_zero⟩
  change C.parameters.Element at a b
  have ha : a.val.val.val < C.modulus := ZMod.val_lt _
  have hb : b.val.val.val < C.modulus := ZMod.val_lt _
  have haWidth : a.val.val.val < 2 ^ (n + 3) := ha.trans C.modulus_lt
  have hbWidth : b.val.val.val < 2 ^ (n + 3) := hb.trans C.modulus_lt
  let p := Machine.Binary.encode (n + 3) C.modulus
  let q := Machine.Binary.encode (n + 3) C.scalarOrder
  let g := Machine.Binary.encode (n + 3) C.generator.val.val
  let aBits := Machine.Binary.encode (n + 3) a.val.val.val
  let bBits := Machine.Binary.encode (n + 3) b.val.val.val
  have hOperand : Machine.Binary.value aBits < Machine.Binary.value p := by
    simpa [aBits, p, Machine.Binary.value_encode haWidth, C.modulus_lt] using ha
  have hWidth : Machine.Binary.value p < 2 ^ p.length := by
    simpa [p, Machine.Binary.value_encode C.modulus_lt] using C.modulus_lt
  have hEval := Machine.FramedProductMultiply.eval_valid_at_budget
    n p q g aBits bBits
      (Machine.Binary.encode_length _ _)
      (by simp [p, q]) (by simp [p, g])
      (by simp [p, aBits]) (by simp [p, bBits])
      hOperand hWidth
  have hNumeric : Machine.evalWithin Machine.FramedProductMultiply.program
      (Machine.encodeSecurityParameter n ++ Machine.frame ((instanceCode n).encode x) ++
        Machine.frame ((elementCode n x).encode a) ++
        Machine.frame ((elementCode n x).encode b))
      (Machine.FramedProductMultiply.validBudget n p q g aBits bBits) =
      PMF.pure (some (Machine.Binary.encode (n + 3)
        (a.val.val.val * b.val.val.val % C.modulus))) := by
    simpa [p, q, g, aBits, bBits,
      PrimeOrderRepresentation.instanceCode,
      PrimeOrderParameters.instanceCode,
      PrimeOrderRepresentation.elementCode,
      PrimeOrderParameters.elementCode,
      Machine.Binary.value_encode haWidth,
      Machine.Binary.value_encode hbWidth,
      Machine.Binary.value_encode C.modulus_lt,
      List.append_assoc] using hEval
  change _ = PMF.pure (some (C.elementCode.encode (C.parameters.mul a b)))
  rw [C.elementCode_mul]
  exact hNumeric

theorem framedMultiply_eval_at_securityBudget (n : Nat) (x : Domain n)
    (a b : (embed n x).params.Element) :
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++
      Machine.frame ((elementCode n x).encode a) ++
      Machine.frame ((elementCode n x).encode b)
    Machine.evalWithin Machine.FramedProductMultiply.program raw
      (Machine.FramedProductMultiply.validSecurityBudget n) =
        PMF.pure (some ((elementCode n x).encode ((embed n x).params.mul a b))) := by
  let C := x.down
  let p := Machine.Binary.encode (n + 3) C.modulus
  let q := Machine.Binary.encode (n + 3) C.scalarOrder
  let g := Machine.Binary.encode (n + 3) C.generator.val.val
  let aBits := Machine.Binary.encode (n + 3) a.val.val.val
  let bBits := Machine.Binary.encode (n + 3) b.val.val.val
  have hBudget := Machine.FramedProductMultiply.validBudget_fixedWidth
    n p q g aBits bBits (Machine.Binary.encode_length _ _)
    (by simp [p, q]) (by simp [p, g])
    (by simp [p, aBits]) (by simp [p, bBits])
  rw [← hBudget]
  exact framedMultiply_eval_at_budget n x a b

/-- The same concrete multiplication code satisfies the primitive's exact
correctness statement at a budget indexed by total input length. The
all-input stopping field of the primitive remains separate. -/
theorem framedMultiply_eval_at_rawBudget (n : Nat) (x : Domain n)
    (a b : (embed n x).params.Element) :
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++
      Machine.frame ((elementCode n x).encode a) ++
      Machine.frame ((elementCode n x).encode b)
    Machine.evalWithin Machine.FramedProductMultiply.program raw
      (Machine.FramedProductMultiply.rawBudget raw.length) =
        PMF.pure (some ((elementCode n x).encode ((embed n x).params.mul a b))) := by
  let C := x.down
  haveI : Fact C.modulus.Prime := ⟨C.modulus_prime⟩
  haveI : NeZero C.modulus := ⟨C.modulus_prime.ne_zero⟩
  change C.parameters.Element at a b
  have ha : a.val.val.val < C.modulus := ZMod.val_lt _
  have hb : b.val.val.val < C.modulus := ZMod.val_lt _
  have haWidth : a.val.val.val < 2 ^ (n + 3) := ha.trans C.modulus_lt
  have hbWidth : b.val.val.val < 2 ^ (n + 3) := hb.trans C.modulus_lt
  let p := Machine.Binary.encode (n + 3) C.modulus
  let q := Machine.Binary.encode (n + 3) C.scalarOrder
  let g := Machine.Binary.encode (n + 3) C.generator.val.val
  let aBits := Machine.Binary.encode (n + 3) a.val.val.val
  let bBits := Machine.Binary.encode (n + 3) b.val.val.val
  have hOperand : Machine.Binary.value aBits < Machine.Binary.value p := by
    simpa [aBits, p, Machine.Binary.value_encode haWidth, C.modulus_lt] using ha
  have hWidth : Machine.Binary.value p < 2 ^ p.length := by
    simpa [p, Machine.Binary.value_encode C.modulus_lt] using C.modulus_lt
  have hEval := Machine.FramedProductMultiply.eval_valid_at_rawBudget
    n p q g aBits bBits
      (Machine.Binary.encode_length _ _)
      (by simp [p, q]) (by simp [p, g])
      (by simp [p, aBits]) (by simp [p, bBits])
      hOperand hWidth
  have hNumeric : Machine.evalWithin Machine.FramedProductMultiply.program
      (Machine.encodeSecurityParameter n ++ Machine.frame ((instanceCode n).encode x) ++
        Machine.frame ((elementCode n x).encode a) ++
        Machine.frame ((elementCode n x).encode b))
      (Machine.FramedProductMultiply.rawBudget
        (Machine.encodeSecurityParameter n ++ Machine.frame ((instanceCode n).encode x) ++
          Machine.frame ((elementCode n x).encode a) ++
          Machine.frame ((elementCode n x).encode b)).length) =
      PMF.pure (some (Machine.Binary.encode (n + 3)
        (a.val.val.val * b.val.val.val % C.modulus))) := by
    simpa [p, q, g, aBits, bBits,
      PrimeOrderRepresentation.instanceCode,
      PrimeOrderParameters.instanceCode,
      PrimeOrderRepresentation.elementCode,
      PrimeOrderParameters.elementCode,
      Machine.Binary.value_encode haWidth,
      Machine.Binary.value_encode hbWidth,
      Machine.Binary.value_encode C.modulus_lt,
      List.append_assoc] using hEval
  change _ = PMF.pure (some (C.elementCode.encode (C.parameters.mul a b)))
  rw [C.elementCode_mul]
  exact hNumeric

/-- The guarded finite multiplier supplies both an all-input stopping budget
and the exact represented group product on valid requests. -/
theorem framedSafeMultiply_eval (n : Nat) (x : Domain n)
    (a b : (embed n x).params.Element) :
    let raw := Machine.encodeSecurityParameter n ++
      Machine.frame ((instanceCode n).encode x) ++
      Machine.frame ((elementCode n x).encode a) ++
      Machine.frame ((elementCode n x).encode b)
    Machine.evalWithin Machine.FramedProductSafeMultiply.program raw
      (Machine.FramedProductSafeMultiply.budget raw.length) =
        PMF.pure (some ((elementCode n x).encode
          ((embed n x).params.mul a b))) := by
  let C := x.down
  haveI : Fact C.modulus.Prime := ⟨C.modulus_prime⟩
  haveI : NeZero C.modulus := ⟨C.modulus_prime.ne_zero⟩
  change C.parameters.Element at a b
  have ha : a.val.val.val < C.modulus := ZMod.val_lt _
  have hb : b.val.val.val < C.modulus := ZMod.val_lt _
  have haWidth : a.val.val.val < 2 ^ (n + 3) := ha.trans C.modulus_lt
  have hbWidth : b.val.val.val < 2 ^ (n + 3) := hb.trans C.modulus_lt
  let p := Machine.Binary.encode (n + 3) C.modulus
  let q := Machine.Binary.encode (n + 3) C.scalarOrder
  let g := Machine.Binary.encode (n + 3) C.generator.val.val
  let aBits := Machine.Binary.encode (n + 3) a.val.val.val
  let bBits := Machine.Binary.encode (n + 3) b.val.val.val
  have hOperand : Machine.Binary.value aBits < Machine.Binary.value p := by
    simpa [aBits, p, Machine.Binary.value_encode haWidth, C.modulus_lt] using ha
  have hWidth : Machine.Binary.value p < 2 ^ p.length := by
    simpa [p, Machine.Binary.value_encode C.modulus_lt] using C.modulus_lt
  have hEval := Machine.FramedProductSafeMultiply.eval_valid
    n p q g aBits bBits
      (Machine.Binary.encode_length _ _)
      (by simp [p, q]) (by simp [p, g])
      (by simp [p, aBits]) (by simp [p, bBits])
      hOperand hWidth
  have hNumeric : Machine.evalWithin Machine.FramedProductSafeMultiply.program
      (Machine.encodeSecurityParameter n ++ Machine.frame ((instanceCode n).encode x) ++
        Machine.frame ((elementCode n x).encode a) ++
        Machine.frame ((elementCode n x).encode b))
      (Machine.FramedProductSafeMultiply.budget
        (Machine.encodeSecurityParameter n ++ Machine.frame ((instanceCode n).encode x) ++
          Machine.frame ((elementCode n x).encode a) ++
          Machine.frame ((elementCode n x).encode b)).length) =
      PMF.pure (some (Machine.Binary.encode (n + 3)
        (a.val.val.val * b.val.val.val % C.modulus))) := by
    simpa [p, q, g, aBits, bBits,
      PrimeOrderRepresentation.instanceCode,
      PrimeOrderParameters.instanceCode,
      PrimeOrderRepresentation.elementCode,
      PrimeOrderParameters.elementCode,
      Machine.Binary.value_encode haWidth,
      Machine.Binary.value_encode hbWidth,
      Machine.Binary.value_encode C.modulus_lt,
      List.append_assoc] using hEval
  change _ = PMF.pure (some (C.elementCode.encode (C.parameters.mul a b)))
  rw [C.elementCode_mul]
  exact hNumeric

/-- The same native model computes encoded group exponentiation from a raw
interleaved residue triple. Its extra high workspace bit is written and
removed by charged machine instructions. -/
theorem rawPower_correct (n : Nat) (x : Domain n)
    (a : (embed n x).params.Element) (s : (embed n x).params.Scalar) :
    let C := x.down
    let raw := Machine.BinaryModularAddition.interleave
      (Machine.BinaryProductExternalWidth.numberColumns (n + 3)
        C.modulus a.val.val.val s.val)
    Machine.evalWithin Machine.BinaryPowerExternalWidth.program raw
      (Machine.BinaryPowerExternalWidth.budget raw.length) =
      PMF.pure (some ((elementCode n x).encode ((embed n x).params.power a s))) := by
  dsimp only
  let C := x.down
  haveI : Fact C.modulus.Prime := ⟨C.modulus_prime⟩
  haveI : NeZero C.modulus := ⟨C.modulus_prime.ne_zero⟩
  change C.parameters.Element at a
  change C.parameters.Scalar at s
  have ha : a.val.val.val < C.modulus := ZMod.val_lt _
  have hs : s.val < 2 ^ (n + 3) :=
    (s.isLt.trans C.scalarOrder_lt_modulus).trans C.modulus_lt
  have hNative := Machine.BinaryPowerExternalWidth.eval_numbers
    (n + 3) C.modulus a.val.val.val s.val C.modulus_prime.one_lt
    ha hs C.modulus_lt
  change Machine.evalWithin Machine.BinaryPowerExternalWidth.program
    (Machine.BinaryModularAddition.interleave
      (Machine.BinaryProductExternalWidth.numberColumns (n + 3)
        C.modulus a.val.val.val s.val))
    (Machine.BinaryPowerExternalWidth.budget
      (Machine.BinaryModularAddition.interleave
        (Machine.BinaryProductExternalWidth.numberColumns (n + 3)
          C.modulus a.val.val.val s.val)).length) =
    PMF.pure (some (C.elementCode.encode (C.parameters.power a s)))
  rw [C.elementCode_power]
  exact hNative

/-- Concrete simulator multiplication witness: one fixed guarded machine
program, a polynomial all-input budget, and exact output on represented
prime-order group elements. -/
noncomputable def simulatorPrimitives :
    RepresentedSimulatorPrimitives sampling Domain embed where
  instanceCode := instanceCode
  instanceCodeLength := fun n => 3 * (n + 3)
  instanceCodeLength_polynomial := by
    exact (PolynomiallyBounded.const 3).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 3))
  instanceCode_length_le := by
    intro n x
    simp
  elementCode := elementCode
  elementCodeLength := fun n => n + 3
  elementCodeLength_polynomial :=
    PolynomiallyBounded.id.add (PolynomiallyBounded.const 3)
  elementCode_length_le := by
    intro n x a
    simp
  multiplyProgram := Machine.FramedProductSafeMultiply.program
  multiplyBudget := Machine.FramedProductSafeMultiply.budget
  multiplyBudget_polynomial :=
    Machine.FramedProductSafeMultiply.budget_polynomiallyBounded
  multiplyHalts := Machine.FramedProductSafeMultiply.haltsWithin
  multiply_correct := framedSafeMultiply_eval

end ElGamal.PrimeOrderRepresentation
