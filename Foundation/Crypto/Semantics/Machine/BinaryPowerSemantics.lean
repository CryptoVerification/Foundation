import Foundation.Crypto.Semantics.Machine.BinaryPowerLoop

set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace Machine.BinaryPowerSemantics

open BinaryProductSelection BinaryProductWorkspace BinaryProductSemantics

/-- Mathematical specification of one exponent-bit update. The executable
implementation squares by calling the native product program and then
conditionally multiplies, or physically copies, the resulting accumulator. -/
def step (modulus operand residue : Nat) (bit : Bool) : Nat :=
  if bit then (residue * residue % modulus * operand) % modulus else residue * residue % modulus

def finishValue (modulus operand residue : Nat) : List Bool → Nat
  | [] => residue
  | bit :: rest => step modulus operand (finishValue modulus operand residue rest) bit

private theorem finishValue_append (modulus operand residue : Nat) (first second : List Bool) :
    finishValue modulus operand residue (first ++ second) =
      finishValue modulus operand (finishValue modulus operand residue second) first := by
  induction first with
  | nil => rfl
  | cons bit rest ih => simp [finishValue, ih]

def power (modulus operand : Nat) : List Bool → Nat
  | [] => 1 % modulus
  | bit :: rest => step modulus operand (power modulus operand rest) bit

theorem finishValue_one (modulus operand : Nat) (bits : List Bool) :
    finishValue modulus operand (1 % modulus) bits = power modulus operand bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [finishValue, power, ih]

theorem power_value (modulus operand : Nat) (bits : List Bool) :
    power modulus operand bits = operand ^ (Binary.value bits) % modulus := by
  induction bits with
  | nil => simp only [power, Binary.value, pow_zero]
  | cons bit rest ih =>
      have hDouble : operand ^ (2 * Binary.value rest) =
          operand ^ Binary.value rest * operand ^ Binary.value rest := by
        calc
          _ = operand ^ (Binary.value rest * 2) := by rw [Nat.mul_comm 2]
          _ = _ := by rw [pow_mul, pow_two]
      cases bit with
      | false =>
          simp [power, step, ih, Binary.value, hDouble, Nat.mul_mod, Nat.mod_mod]
      | true =>
          simp [power, step, ih, Binary.value, pow_add, hDouble,
            Nat.mul_mod, Nat.mod_mod]
          congr 1
          ring

/-- Exact output certificates from the native multiplication/copy calls
establish the square-and-multiply numerical update. -/
theorem outputs_value (columns : List Column) (bit : Bool)
    (doubleBits addBits : List Bool)
    (hDoubleLength : doubleBits.length = columns.length)
    (hAddLength : addBits.length = columns.length)
    (hDouble : evalWithin BinaryProductProgram.program
      (BinarySquareGather.request (consume columns.reverse).reverse)
      (BinaryProductProgram.budget (BinarySquareGather.request (consume columns.reverse).reverse).length) = PMF.pure (some doubleBits))
    (hAdd : evalWithin (BinaryPowerPhase.conditionalKernel bit)
      (BinaryPowerPhase.conditionalRequest bit (replaceAccumulator (consume columns.reverse).reverse doubleBits))
      (BinaryPowerPhase.conditionalKernelBudget bit
        (BinaryPowerPhase.conditionalRequest bit (replaceAccumulator (consume columns.reverse).reverse doubleBits)).length) = PMF.pure (some addBits))
    (hResidue : Binary.value (columns.map Column.accumulator) < Binary.value (columns.map Column.modulus))
    (hOperand : Binary.value (columns.map Column.operand) < Binary.value (columns.map Column.modulus))
    (hRoom : 2 * Binary.value (columns.map Column.modulus) ≤ 2 ^ columns.length) :
    Binary.value addBits = step
      (Binary.value (columns.map Column.modulus)) (Binary.value (columns.map Column.operand))
      (Binary.value (columns.map Column.accumulator)) bit := by
  let consumed := (consume columns.reverse).reverse
  let intermediate := replaceAccumulator consumed doubleBits
  let residue := Binary.value (columns.map Column.accumulator)
  let operand := Binary.value (columns.map Column.operand)
  let modulus := Binary.value (columns.map Column.modulus)
  have hPositive : 0 < modulus := by dsimp only [modulus]; omega
  have hModWidth : modulus < 2 ^ columns.length := by dsimp only [modulus]; omega
  have hConsumed : consumed.length = columns.length := by simp [consumed, consume_length]
  have hd : doubleBits.length = consumed.length := hDoubleLength.trans hConsumed.symm
  have hAcc : consumed.map Column.accumulator = columns.map Column.accumulator := consumed_map _ (fun _ => rfl) _
  have hMod : consumed.map Column.modulus = columns.map Column.modulus := consumed_map _ (fun _ => rfl) _
  have hOp : consumed.map Column.operand = columns.map Column.operand := consumed_map _ (fun _ => rfl) _
  have expectedSquare := eval_product_encoded
    (consumed.map fun column => ((column.accumulator, column.accumulator), column.modulus))
    (by simpa [List.map_map, Function.comp_def, hAcc, hMod] using hResidue)
    (by simpa [List.map_map, Function.comp_def, hMod, hConsumed] using hRoom)
  have squareExact : doubleBits = Binary.encode columns.length (residue * residue % modulus) := by
    apply result_unique
    exact hDouble.symm.trans (by simpa only [BinarySquareGather.request, List.length_map,
      List.map_map, Function.comp_def, hConsumed, hAcc, hMod, residue, modulus] using expectedSquare)
  have squareValue : Binary.value doubleBits = residue * residue % modulus := by
    rw [squareExact, Binary.value_encode ((Nat.mod_lt _ hPositive).trans hModWidth)]
  have hIntermediate : intermediate.length = columns.length := by simp [intermediate, replaceAccumulator, hConsumed, hDoubleLength]
  have hIntermediateAcc : intermediate.map Column.accumulator = doubleBits := replace_accumulator _ _ hd
  have hIntermediateMod : intermediate.map Column.modulus = columns.map Column.modulus :=
    (replace_map _ (fun _ _ => rfl) _ _ hd).trans hMod
  have hIntermediateOp : intermediate.map Column.operand = columns.map Column.operand :=
    (replace_map _ (fun _ _ => rfl) _ _ hd).trans hOp
  cases bit with
  | false =>
      have hCopy := copyBitstring_eval (intermediate.map Column.accumulator)
      have exactCopy : addBits = intermediate.map Column.accumulator := result_unique _ _ (hAdd.symm.trans hCopy)
      rw [exactCopy, hIntermediateAcc, squareValue]
      rfl
  | true =>
      have expectedProduct := eval_product_encoded
        (intermediate.map fun column => ((column.accumulator, column.operand), column.modulus))
        (by simpa [List.map_map, Function.comp_def, hIntermediateAcc, hIntermediateMod, squareValue, modulus]
          using Nat.mod_lt (residue * residue) hPositive)
        (by simpa [List.map_map, Function.comp_def, hIntermediateMod, hIntermediate] using hRoom)
      have productExact : addBits = Binary.encode columns.length ((residue * residue % modulus * operand) % modulus) := by
        apply result_unique
        exact hAdd.symm.trans (by simpa only [BinaryPowerPhase.conditionalKernel, BinaryPowerPhase.conditionalRequest,
          BinaryPowerPhase.conditionalKernelBudget, BinaryPowerPhase.multiplyRequest, BinaryProductPhase.addRequest,
          List.length_map, List.map_map, Function.comp_def, hIntermediateAcc, hIntermediateMod, hIntermediateOp, hIntermediate,
          squareValue, operand, modulus, Bool.true_eq, ite_true] using expectedProduct)
      rw [productExact, Binary.value_encode ((Nat.mod_lt _ hPositive).trans hModWidth)]
      rfl

/-- Numerical invariants attached to the actual native iteration trace. -/
theorem iteration_correct (columns : List Column) (saved : List (Option Bool)) (bit : Bool)
    (hSelected : selected columns.reverse = some bit)
    (hResidue : Binary.value (columns.map Column.accumulator) < Binary.value (columns.map Column.modulus))
    (hOperand : Binary.value (columns.map Column.operand) < Binary.value (columns.map Column.modulus))
    (hRoom : 2 * Binary.value (columns.map Column.modulus) ≤ 2 ^ columns.length) :
    ∃ (nextColumns : List Column) (nextSaved : List (Option Bool))
      (target : Configuration) (used : Nat),
      nextColumns.length = columns.length ∧
      pendingCount nextColumns = pendingCount columns - 1 ∧
      used ≤ BinaryPowerLoop.iterationBudget columns.length ∧
      RunsFor BinaryPowerLoop.program (BinaryPowerLoop.start columns saved) target used ∧
      target.Equivalent (BinaryPowerLoop.start nextColumns nextSaved) ∧
      nextColumns.map Column.modulus = columns.map Column.modulus ∧
      nextColumns.map Column.operand = columns.map Column.operand ∧
      remainingBits columns = remainingBits nextColumns ++ [bit] ∧
      Binary.value (nextColumns.map Column.accumulator) = step
        (Binary.value (columns.map Column.modulus)) (Binary.value (columns.map Column.operand))
        (Binary.value (columns.map Column.accumulator)) bit := by
  obtain ⟨nextColumns, nextSaved, target, used, hWidth, hPending, hUsed, native, layout,
    doubleBits, addBits, hDoubleLength, hAddLength, hNext, hDouble, hAdd⟩ :=
    BinaryPowerLoop.iteration columns saved bit hSelected
  let consumed := (consume columns.reverse).reverse
  let intermediate := replaceAccumulator consumed doubleBits
  have hConsumed : consumed.length = columns.length := by simp [consumed, consume_length]
  have hd : doubleBits.length = consumed.length := hDoubleLength.trans hConsumed.symm
  have hi : intermediate.length = columns.length :=
    by simp [intermediate, replaceAccumulator, hDoubleLength, hConsumed]
  have ha : addBits.length = intermediate.length := hAddLength.trans hi.symm
  have modMap : nextColumns.map Column.modulus = columns.map Column.modulus := by
    rw [hNext, replace_map _ (fun _ _ => rfl) _ _ ha,
      replace_map _ (fun _ _ => rfl) _ _ hd, consumed_map _ (fun _ => rfl)]
  have opMap : nextColumns.map Column.operand = columns.map Column.operand := by
    rw [hNext, replace_map _ (fun _ _ => rfl) _ _ ha,
      replace_map _ (fun _ _ => rfl) _ _ hd, consumed_map _ (fun _ => rfl)]
  have remMap : remainingBits nextColumns = remainingBits consumed := by
    rw [hNext, replace_remaining _ _ ha, replace_remaining _ _ hd]
  have accMap : nextColumns.map Column.accumulator = addBits := by
    rw [hNext, replace_accumulator _ _ ha]
  refine ⟨nextColumns, nextSaved, target, used, hWidth, hPending, hUsed, native, layout,
    modMap, opMap, ?_, ?_⟩
  · rw [remMap]
    exact consumed_remaining columns bit hSelected
  · rw [accMap]
    exact outputs_value columns bit doubleBits addBits hDoubleLength hAddLength hDouble hAdd
      hResidue hOperand hRoom

/-- Complete numerical correctness follows the same physical program trace
as the all-input stopping proof. The mathematical induction consumes the
stored pending flags; it introduces no extra arithmetic machine instruction. -/
theorem runs_correct (columns : List Column) (saved : List (Option Bool))
    (hResidue : Binary.value (columns.map Column.accumulator) < Binary.value (columns.map Column.modulus))
    (hOperand : Binary.value (columns.map Column.operand) < Binary.value (columns.map Column.modulus))
    (hRoom : 2 * Binary.value (columns.map Column.modulus) ≤ 2 ^ columns.length) :
    ∃ (finalColumns : List Column) (finalSaved : List (Option Bool))
      (target : Configuration) (used : Nat),
      finalColumns.length = columns.length ∧
      used ≤ BinaryPowerLoop.budget columns.length (pendingCount columns) ∧
      RunsFor BinaryPowerLoop.program (BinaryPowerLoop.start columns saved) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent { right := (matrix finalColumns).map some ++ [none] } ∧
      target.outputTape.Equivalent { left := finalSaved } ∧
      Binary.value (finalColumns.map Column.accumulator) = finishValue
        (Binary.value (columns.map Column.modulus)) (Binary.value (columns.map Column.operand))
        (Binary.value (columns.map Column.accumulator)) (remainingBits columns) := by
  have main (count : Nat) : ∀ (columns : List Column) (saved : List (Option Bool)),
      pendingCount columns = count →
      Binary.value (columns.map Column.accumulator) < Binary.value (columns.map Column.modulus) →
      Binary.value (columns.map Column.operand) < Binary.value (columns.map Column.modulus) →
      2 * Binary.value (columns.map Column.modulus) ≤ 2 ^ columns.length →
      ∃ (finalColumns : List Column) (finalSaved : List (Option Bool))
        (target : Configuration) (used : Nat),
        finalColumns.length = columns.length ∧
        used ≤ BinaryPowerLoop.budget columns.length count ∧
        RunsFor BinaryPowerLoop.program (BinaryPowerLoop.start columns saved) target used ∧
        target.halted = true ∧
        target.inputTape.Equivalent { right := (matrix finalColumns).map some ++ [none] } ∧
        target.outputTape.Equivalent { left := finalSaved } ∧
        Binary.value (finalColumns.map Column.accumulator) = finishValue
          (Binary.value (columns.map Column.modulus)) (Binary.value (columns.map Column.operand))
          (Binary.value (columns.map Column.accumulator)) (remainingBits columns) := by
    induction count using Nat.strong_induction_on with
    | h count ih =>
        intro columns saved hCount hResidue hOperand hRoom
        cases hSelected : selected columns.reverse with
        | none =>
            have hZero : pendingCount columns = 0 := by
              simpa only [pendingCount_reverse] using (selected_none_iff _).mp hSelected
            have hRemaining : remainingBits columns = [] := List.length_eq_zero_iff.mp
              ((remaining_length columns).trans hZero)
            obtain ⟨target, used, hUsed, native, hHalt, hInput, hOutput⟩ :=
              BinaryPowerLoop.exhausted columns saved hSelected
            refine ⟨columns, saved, target, used, rfl, ?_, native, hHalt, hInput, hOutput, ?_⟩
            · dsimp only [BinaryPowerLoop.budget, BinaryPowerLoop.iterationBudget]
              have hc : count = 0 := hCount.symm.trans hZero
              rw [hc]
              omega
            · rw [hRemaining]; rfl
        | some bit =>
            have hPositive : 0 < pendingCount columns := by
              by_contra hNot
              have hZero : pendingCount columns.reverse = 0 := by rw [pendingCount_reverse]; omega
              have hNone := (selected_none_iff _).mpr hZero
              simp [hSelected] at hNone
            obtain ⟨nextColumns, nextSaved, middle, firstTime, hWidth, hPending, hFirst,
              firstRun, middleLayout, hMod, hOp, hRemaining, hAcc⟩ :=
              iteration_correct columns saved bit hSelected hResidue hOperand hRoom
            have hLess : pendingCount nextColumns < count := by omega
            have hNextResidue : Binary.value (nextColumns.map Column.accumulator) <
                Binary.value (nextColumns.map Column.modulus) := by
              rw [hMod, hAcc]
              cases bit <;> simp only [step, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] <;> exact Nat.mod_lt _ (by omega)
            obtain ⟨finalColumns, finalSaved, canonical, lastTime, hFinalWidth,
              hLast, lastRun, hHalt, hInput, hOutput, hValue⟩ := ih _ hLess nextColumns nextSaved rfl
                hNextResidue (by simpa only [hMod, hOp] using hOperand)
                (by simpa only [hMod, hWidth] using hRoom)
            obtain ⟨target, actualLast, targetLayout⟩ := lastRun.exists_equivalent middleLayout.symm
            refine ⟨finalColumns, finalSaved, target, firstTime + lastTime,
              hFinalWidth.trans hWidth, ?_, firstRun.trans actualLast, ?_, ?_, ?_, ?_⟩
            · rw [hWidth, hPending] at hLast
              have hc : pendingCount columns = (pendingCount columns - 1) + 1 := by omega
              calc
                firstTime + lastTime ≤ BinaryPowerLoop.iterationBudget columns.length +
                    BinaryPowerLoop.budget columns.length (pendingCount columns - 1) := Nat.add_le_add hFirst hLast
                _ ≤ BinaryPowerLoop.budget columns.length count := by
                  rw [← hCount]
                  dsimp only [BinaryPowerLoop.budget]
                  rw [← hc]
                  nlinarith
            · exact targetLayout.2.1.symm.trans hHalt
            · exact targetLayout.2.2.1.symm.trans hInput
            · exact targetLayout.2.2.2.symm.trans hOutput
            · rw [hValue, hRemaining, finishValue_append]
              simp only [finishValue, hMod, hOp, hAcc]
  exact main _ columns saved rfl hResidue hOperand hRoom

end Machine.BinaryPowerSemantics
