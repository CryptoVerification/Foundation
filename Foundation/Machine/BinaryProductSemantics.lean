import Foundation.Machine.BinaryProductProgram
import Foundation.Machine.BinaryModularProduct

namespace Machine.BinaryProductSemantics

open BinaryProductSelection BinaryProductWorkspace

def remainingBits (columns : List Column) : List Bool :=
  columns.filterMap fun column => if column.pending then some column.multiplier else none

/-- Mathematical value of the unprocessed multiplier suffix, starting
from the current accumulator. This is a specification, not an instruction
that performs arithmetic on a whole natural number. -/
def finishValue (modulus operand residue : Nat) : List Bool → Nat
  | [] => residue
  | bit :: rest => BinaryModularProduct.step modulus operand (finishValue modulus operand residue rest) bit

private theorem finishValue_append (modulus operand residue : Nat) (first second : List Bool) :
    finishValue modulus operand residue (first ++ second) =
      finishValue modulus operand (finishValue modulus operand residue second) first := by
  induction first with
  | nil => rfl
  | cons bit rest ih => simp [finishValue, ih]

private theorem consume_map {α : Type} (project : Column → α)
    (hProject : ∀ column, project { column with pending := false } = project column)
    (columns : List Column) : (consume columns).map project = columns.map project := by
  induction columns with
  | nil => rfl
  | cons column rest ih => simp only [consume]; split <;> simp [hProject, ih]

theorem consumed_map {α : Type} (project : Column → α)
    (hProject : ∀ column, project { column with pending := false } = project column)
    (columns : List Column) : ((consume columns.reverse).reverse).map project = columns.map project := by
  rw [List.map_reverse, consume_map project hProject, List.map_reverse, List.reverse_reverse]

theorem replace_map {α : Type} (project : Column → α)
    (hProject : ∀ column bit, project { column with accumulator := bit } = project column)
    (columns : List Column) (bits : List Bool) (hLength : bits.length = columns.length) :
    (replaceAccumulator columns bits).map project = columns.map project := by
  induction columns generalizing bits with
  | nil =>
      have empty : bits = [] := by simpa using hLength
      subst bits
      rfl
  | cons column rest ih =>
      cases bits with
      | nil => simp at hLength
      | cons bit remaining =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hLength
          change project { column with accumulator := bit } ::
            (replaceAccumulator rest remaining).map project = project column :: rest.map project
          rw [hProject, ih remaining hLength]

theorem replace_accumulator (columns : List Column) (bits : List Bool)
    (hLength : bits.length = columns.length) :
    (replaceAccumulator columns bits).map Column.accumulator = bits := by
  induction columns generalizing bits with
  | nil =>
      have empty : bits = [] := by simpa using hLength
      subst bits
      rfl
  | cons column rest ih =>
      cases bits with
      | nil => simp at hLength
      | cons bit remaining =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hLength
          change bit :: (replaceAccumulator rest remaining).map Column.accumulator = bit :: remaining
          rw [ih remaining hLength]

theorem replace_remaining (columns : List Column) (bits : List Bool)
    (hLength : bits.length = columns.length) :
    remainingBits (replaceAccumulator columns bits) = remainingBits columns := by
  induction columns generalizing bits with
  | nil =>
      have empty : bits = [] := by simpa using hLength
      subst bits
      rfl
  | cons column rest ih =>
      cases bits with
      | nil => simp at hLength
      | cons bit remaining =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hLength
          cases hPending : column.pending with
          | false =>
              simpa only [replaceAccumulator, remainingBits, List.zipWith_cons_cons,
                List.filterMap_cons, hPending, Bool.false_eq_true, ↓reduceIte] using ih remaining hLength
          | true =>
              have h := congrArg (List.cons column.multiplier) (ih remaining hLength)
              simpa only [replaceAccumulator, remainingBits, List.zipWith_cons_cons,
                List.filterMap_cons, hPending, ↓reduceIte] using h

private theorem remaining_reverse (columns : List Column) :
    remainingBits columns.reverse = (remainingBits columns).reverse := by
  simp [remainingBits, List.filterMap_reverse]

private theorem consume_remaining (columns : List Column) (bit : Bool)
    (hSelected : selected columns = some bit) :
    remainingBits columns = bit :: remainingBits (consume columns) := by
  induction columns with
  | nil => simp [selected] at hSelected
  | cons column rest ih =>
      cases hPending : column.pending with
      | true =>
          have hBit : column.multiplier = bit := by simpa [selected, hPending] using hSelected
          simp [remainingBits, consume, hPending, hBit]
      | false =>
          have hRest : selected rest = some bit := by simpa [selected, hPending] using hSelected
          simpa [remainingBits, consume, hPending] using ih hRest

theorem consumed_remaining (columns : List Column) (bit : Bool)
    (hSelected : selected columns.reverse = some bit) :
    remainingBits columns = remainingBits (consume columns.reverse).reverse ++ [bit] := by
  have h := congrArg List.reverse (consume_remaining columns.reverse bit hSelected)
  simpa only [remaining_reverse, List.reverse_reverse, List.reverse_cons] using h

theorem remaining_length (columns : List Column) :
    (remainingBits columns).length = pendingCount columns := by
  induction columns with
  | nil => rfl
  | cons column rest ih =>
      cases hPending : column.pending
      · simpa [remainingBits, pendingCount, hPending] using ih
      · simpa [remainingBits, pendingCount, hPending] using ih

private theorem zero_value {α : Type} (columns : List α) : Binary.value (columns.map fun _ => false) = 0 := by
  induction columns with
  | nil => rfl
  | cons column rest ih => simp only [List.map_cons, Binary.value, Bool.toNat_false, ih, Nat.mul_zero, Nat.add_zero]

theorem result_unique (first second : List Bool)
    (h : PMF.pure (some first) = PMF.pure (some second)) : first = second := by
  have member : some first ∈ (PMF.pure (some second)).support := by rw [← h]; simp
  simpa using member

/-- The arithmetic certificates returned by the native iteration establish
the value of its actual updated accumulator. All other numerical tracks
remain unchanged, and the selected bit is removed from the pending suffix. -/
theorem outputs_value (columns : List Column) (bit : Bool)
    (doubleBits addBits : List Bool)
    (hDoubleLength : doubleBits.length = columns.length)
    (hAddLength : addBits.length = columns.length)
    (hDouble : evalWithin BinaryDoubleReduction.program
      (BinaryProductPhase.doubleRequest (consume columns.reverse).reverse)
      (18 * columns.length + 15) = PMF.pure (some doubleBits))
    (hAdd : evalWithin BinaryModularAddition.program
      (BinaryProductPhase.addRequest bit (replaceAccumulator (consume columns.reverse).reverse doubleBits))
      (24 * columns.length + 10) = PMF.pure (some addBits))
    (hResidue : Binary.value (columns.map Column.accumulator) < Binary.value (columns.map Column.modulus))
    (hOperand : Binary.value (columns.map Column.operand) < Binary.value (columns.map Column.modulus))
    (hRoom : 2 * Binary.value (columns.map Column.modulus) ≤ 2 ^ columns.length) :
    Binary.value addBits = BinaryModularProduct.step
      (Binary.value (columns.map Column.modulus)) (Binary.value (columns.map Column.operand))
      (Binary.value (columns.map Column.accumulator)) bit := by
  let consumed := (consume columns.reverse).reverse
  let intermediate := replaceAccumulator consumed doubleBits
  let residue := Binary.value (columns.map Column.accumulator)
  let operand := Binary.value (columns.map Column.operand)
  let modulus := Binary.value (columns.map Column.modulus)
  have hPositive : 0 < modulus := by dsimp only [modulus]; omega
  have hRoom' : 2 * modulus ≤ 2 ^ columns.length := hRoom
  have hConsumed : consumed.length = columns.length := by simp [consumed, consume_length]
  have hDoubleLength' : doubleBits.length = consumed.length := hDoubleLength.trans hConsumed.symm
  have hAcc : consumed.map Column.accumulator = columns.map Column.accumulator := consumed_map _ (fun _ => rfl) _
  have hMod : consumed.map Column.modulus = columns.map Column.modulus := consumed_map _ (fun _ => rfl) _
  have hOp : consumed.map Column.operand = columns.map Column.operand := consumed_map _ (fun _ => rfl) _
  let pairs := consumed.map fun column => (column.accumulator, column.modulus)
  have hPairsAcc : pairs.map Prod.fst = columns.map Column.accumulator := by
    simpa [pairs, List.map_map, Function.comp_def] using hAcc
  have hPairsMod : pairs.map Prod.snd = columns.map Column.modulus := by
    simpa [pairs, List.map_map, Function.comp_def] using hMod
  have expectedDouble := BinaryDoubleReduction.eval_double_mod_encoded false pairs
    (by simpa only [hPairsAcc, hPairsMod] using hResidue)
    (by simp only [hPairsAcc, pairs, List.length_map, hConsumed, Bool.toNat_false, Nat.add_zero]; omega)
  have doubleExact : doubleBits = Binary.encode columns.length ((2 * residue) % modulus) := by
    apply result_unique
    exact hDouble.symm.trans (by simpa only [pairs, List.length_map, hConsumed, hPairsAcc, hPairsMod,
      Bool.toNat_false, Nat.add_zero, BinaryProductPhase.doubleRequest, consumed, residue, modulus] using expectedDouble)
  have hDoubleSmall : (2 * residue) % modulus < modulus := Nat.mod_lt _ hPositive
  have hModWidth : modulus < 2 ^ columns.length := by dsimp only [modulus]; omega
  have doubleValue : Binary.value doubleBits = (2 * residue) % modulus := by
    rw [doubleExact, Binary.value_encode (hDoubleSmall.trans hModWidth)]
  have hIntermediate : intermediate.length = columns.length := by simp [intermediate, replaceAccumulator, hConsumed, hDoubleLength]
  have hIntermediateAcc : intermediate.map Column.accumulator = doubleBits := replace_accumulator _ _ hDoubleLength'
  have hIntermediateMod : intermediate.map Column.modulus = columns.map Column.modulus :=
    (replace_map _ (fun _ _ => rfl) _ _ hDoubleLength').trans hMod
  have hIntermediateOp : intermediate.map Column.operand = columns.map Column.operand :=
    (replace_map _ (fun _ _ => rfl) _ _ hDoubleLength').trans hOp
  let triples := intermediate.map fun column =>
    ((column.accumulator, if bit then column.operand else false), column.modulus)
  have hFirst : Binary.value ((BinaryModularAddition.operands triples).map Prod.fst) = (2 * residue) % modulus := by
    simpa [triples, BinaryModularAddition.operands, List.map_map, Function.comp_def, hIntermediateAcc] using doubleValue
  have hSecond : Binary.value ((BinaryModularAddition.operands triples).map Prod.snd) =
      if bit then operand else 0 := by
    cases bit with
    | false => simpa [triples, BinaryModularAddition.operands, List.map_map, Function.comp_def] using zero_value intermediate
    | true => simp [triples, BinaryModularAddition.operands, List.map_map, Function.comp_def, hIntermediateOp, operand]
  have hModulus : Binary.value (BinaryModularAddition.moduli triples) = modulus := by
    simp [triples, BinaryModularAddition.moduli, List.map_map, Function.comp_def, hIntermediateMod, modulus]
  have hSelectedSmall : (if bit then operand else 0) < modulus := by
    cases bit
    · exact hPositive
    · exact hOperand
  have expectedAdd := BinaryModularAddition.eval_add_mod_encoded triples
    (by rw [hFirst, hModulus]; exact hDoubleSmall)
    (by rw [hSecond, hModulus]; exact hSelectedSmall)
    (by rw [hFirst, hSecond]; simp only [triples, List.length_map, hIntermediate]; omega)
  have addExact : addBits = Binary.encode columns.length
      (((2 * residue) % modulus + if bit then operand else 0) % modulus) := by
    apply result_unique
    exact hAdd.symm.trans (by simpa only [hFirst, hSecond, hModulus, triples, List.length_map,
      hIntermediate, BinaryProductPhase.addRequest, intermediate, consumed] using expectedAdd)
  rw [addExact, Binary.value_encode ((Nat.mod_lt _ hPositive).trans hModWidth)]
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
      used ≤ BinaryProductLoop.iterationBudget columns.length ∧
      RunsFor BinaryProductLoop.program (BinaryProductLoop.start columns saved) target used ∧
      target.Equivalent (BinaryProductLoop.start nextColumns nextSaved) ∧
      nextColumns.map Column.modulus = columns.map Column.modulus ∧
      nextColumns.map Column.operand = columns.map Column.operand ∧
      remainingBits columns = remainingBits nextColumns ++ [bit] ∧
      Binary.value (nextColumns.map Column.accumulator) = BinaryModularProduct.step
        (Binary.value (columns.map Column.modulus)) (Binary.value (columns.map Column.operand))
        (Binary.value (columns.map Column.accumulator)) bit := by
  obtain ⟨nextColumns, nextSaved, target, used, hWidth, hPending, hUsed, native, layout,
    doubleBits, addBits, hDoubleLength, hAddLength, hNext, hDouble, hAdd⟩ :=
    BinaryProductLoop.iteration columns saved bit hSelected
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
      used ≤ BinaryProductLoop.budget columns.length (pendingCount columns) ∧
      RunsFor BinaryProductLoop.program (BinaryProductLoop.start columns saved) target used ∧
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
        used ≤ BinaryProductLoop.budget columns.length count ∧
        RunsFor BinaryProductLoop.program (BinaryProductLoop.start columns saved) target used ∧
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
              BinaryProductLoop.exhausted columns saved hSelected
            refine ⟨columns, saved, target, used, rfl, ?_, native, hHalt, hInput, hOutput, ?_⟩
            · dsimp only [BinaryProductLoop.budget, BinaryProductLoop.iterationBudget]
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
              exact Nat.mod_lt _ (by omega)
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
                firstTime + lastTime ≤ BinaryProductLoop.iterationBudget columns.length +
                    BinaryProductLoop.budget columns.length (pendingCount columns - 1) := Nat.add_le_add hFirst hLast
                _ ≤ BinaryProductLoop.budget columns.length count := by
                  rw [← hCount]
                  dsimp only [BinaryProductLoop.budget]
                  rw [← hc]
                  nlinarith
            · exact targetLayout.2.1.symm.trans hHalt
            · exact targetLayout.2.2.1.symm.trans hInput
            · exact targetLayout.2.2.2.symm.trans hOutput
            · rw [hValue, hRemaining, finishValue_append]
              simp only [finishValue, hMod, hOp, hAcc]
  exact main _ columns saved rfl hResidue hOperand hRoom

private theorem finishValue_zero (modulus operand : Nat) (bits : List Bool) :
    finishValue modulus operand 0 bits = BinaryModularProduct.product modulus operand bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [finishValue, BinaryModularProduct.product, ih]

theorem interleave_length (columns : List BinaryModularAddition.Column) :
    (BinaryModularAddition.interleave columns).length = 3 * columns.length := by
  induction columns with
  | nil => rfl
  | cons column rest ih => simp [BinaryModularAddition.interleave, ih]; omega

/-- The full fixed finite program computes a modular product on complete
little-endian columns. Its budget is the same all-input polynomial bound;
initialization, arithmetic calls, rewinds, copies, and erasure are included. -/
theorem eval_product_encoded (columns : List BinaryModularAddition.Column)
    (hOperand : Binary.value (columns.map fun c => c.1.1) < Binary.value (columns.map Prod.snd))
    (hRoom : 2 * Binary.value (columns.map Prod.snd) ≤ 2 ^ columns.length) :
    evalWithin BinaryProductProgram.program (BinaryModularAddition.interleave columns)
      (BinaryProductProgram.budget (BinaryModularAddition.interleave columns).length) =
      PMF.pure (some (Binary.encode columns.length
        (Binary.value (columns.map fun c => c.1.1) * Binary.value (columns.map fun c => c.1.2) %
          Binary.value (columns.map Prod.snd)))) := by
  let input := BinaryModularAddition.interleave columns
  let initialized : Configuration :=
    { pc := 116, inputTape := { left := input.reverse.map some },
      outputTape := { left := (BinaryProductInitialization.matrix columns).reverse.map some }, halted := true }
  have hEval : evalConfigWithin BinaryProductInitialization.program (Configuration.initial input)
      (17 * columns.length + 2) = PMF.pure initialized := by
    have emptyStart : BinaryProductInitialization.initializationStart [] [] input = Configuration.initial input := by
      cases input <;> rfl
    have h := BinaryProductInitialization.eval_interleave_context columns [] []
    change evalConfigWithin _ (BinaryProductInitialization.initializationStart [] [] input) _ = _ at h
    rw [emptyStart] at h
    simpa only [List.append_nil] using h
  have hPad : evalConfigWithin BinaryProductInitialization.program (Configuration.initial input)
      (17 * (input.length + 1)) = PMF.pure initialized := by
    rw [evalConfigWithin_eq_of_le _ _ (17 * columns.length + 2) _
      (by simp only [input, interleave_length]; omega)]
    · exact hEval
    · intro target trace
      have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
      rw [hEval, PMF.mem_support_pure_iff] at member
      exact member ▸ rfl
  let initial := initialColumns columns
  have hWidth : initial.length = columns.length := by simp [initial, initialColumns]
  have hAcc : Binary.value (initial.map Column.accumulator) = 0 := by
    simpa only [initial, initialColumns, List.map_map, Function.comp_def] using zero_value columns
  have hMod : initial.map Column.modulus = columns.map Prod.snd := by
    simp [initial, initialColumns, List.map_map, Function.comp_def]
  have hOp : initial.map Column.operand = columns.map fun c => c.1.1 := by
    simp [initial, initialColumns, List.map_map, Function.comp_def]
  have hRemaining : remainingBits initial = columns.map fun c => c.1.2 := by
    simp [remainingBits, initial, initialColumns, List.filterMap_map, Function.comp_def]
  obtain ⟨finalColumns, finalSaved, loopTarget, loopSteps, hFinalWidth, hLoopBound,
    loopRun, hLoopHalt, hLoopInput, hLoopOutput, hValue⟩ := runs_correct initial (input.reverse.map some)
      (by rw [hAcc, hMod]; omega) (by simpa only [hOp, hMod] using hOperand)
      (by simpa only [hMod, hWidth] using hRoom)
  obtain ⟨target, used, hUsed, native, hHalt, hOutput, _⟩ :=
    BinaryProductProgram.runs_from_components input columns initialized
      (by simp only [input, interleave_length]; omega) rfl rfl rfl hPad
      finalColumns finalSaved loopTarget loopSteps hFinalWidth hLoopBound loopRun hLoopHalt hLoopInput hLoopOutput
  have hBits : finalColumns.map Column.accumulator = Binary.encode columns.length
      (Binary.value (columns.map fun c => c.1.1) * Binary.value (columns.map fun c => c.1.2) %
        Binary.value (columns.map Prod.snd)) := by
    have he := Binary.encode_value (finalColumns.map Column.accumulator)
    rw [List.length_map, hFinalWidth, hWidth, hValue, hMod, hOp, hAcc, hRemaining,
      finishValue_zero, BinaryModularProduct.product_value] at he
    exact he.symm
  have halts : HaltsWith BinaryProductProgram.program input
      (Binary.encode columns.length
        (Binary.value (columns.map fun c => c.1.1) * Binary.value (columns.map fun c => c.1.2) %
          Binary.value (columns.map Prod.snd))) used :=
    ⟨target, native, hHalt, hOutput.trans hBits⟩
  exact (evalWithin_eq_of_haltsWithin _ input used _
    (halts.haltsWithin_of_no_randomBit BinaryProductProgram.no_randomBit)
    (BinaryProductProgram.haltsWithin input)).symm.trans
      (halts.evalWithin_eq_pure_of_no_randomBit BinaryProductProgram.no_randomBit)

/-- Complete columns always produce one result bit per column, even if their
numeric operands or modulus are invalid. This width certificate allows an
outer native arithmetic loop to reuse the physical workspace safely. -/
theorem complete_output (columns : List BinaryModularAddition.Column) :
    ∃ bits : List Bool, bits.length = columns.length ∧
      evalWithin BinaryProductProgram.program (BinaryModularAddition.interleave columns)
        (BinaryProductProgram.budget (BinaryModularAddition.interleave columns).length) = PMF.pure (some bits) := by
  let input := BinaryModularAddition.interleave columns
  let initialized : Configuration :=
    { pc := 116, inputTape := { left := input.reverse.map some },
      outputTape := { left := (BinaryProductInitialization.matrix columns).reverse.map some }, halted := true }
  have emptyStart : BinaryProductInitialization.initializationStart [] [] input = Configuration.initial input := by
    cases input <;> rfl
  have hEval := BinaryProductInitialization.eval_interleave_context columns [] []
  change evalConfigWithin _ (BinaryProductInitialization.initializationStart [] [] input) _ = _ at hEval
  rw [emptyStart] at hEval
  have hEval' : evalConfigWithin BinaryProductInitialization.program (Configuration.initial input)
      (17 * columns.length + 2) = PMF.pure initialized := by simpa only [List.append_nil] using hEval
  have hPad : evalConfigWithin BinaryProductInitialization.program (Configuration.initial input)
      (17 * (input.length + 1)) = PMF.pure initialized := by
    rw [evalConfigWithin_eq_of_le _ _ (17 * columns.length + 2) _
      (by simp only [input, interleave_length]; omega)]
    · exact hEval'
    · intro target trace
      have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
      rw [hEval', PMF.mem_support_pure_iff] at member
      exact member ▸ rfl
  obtain ⟨finalColumns, finalSaved, loopTarget, loopSteps, hFinalWidth, _, hLoopBound,
    loopRun, hLoopHalt, hLoopInput, hLoopOutput⟩ :=
    BinaryProductLoop.runs (initialColumns columns) (input.reverse.map some)
  obtain ⟨target, used, hUsed, native, hHalt, hOutput, _⟩ :=
    BinaryProductProgram.runs_from_components input columns initialized
      (by simp only [input, interleave_length]; omega) rfl rfl rfl hPad
      finalColumns finalSaved loopTarget loopSteps hFinalWidth hLoopBound loopRun hLoopHalt hLoopInput hLoopOutput
  let bits := finalColumns.map Column.accumulator
  have halts : HaltsWith BinaryProductProgram.program input bits used := ⟨target, native, hHalt, hOutput⟩
  refine ⟨bits, by simp only [bits, List.length_map, hFinalWidth, initialColumns, List.length_map], ?_⟩
  exact (evalWithin_eq_of_haltsWithin _ input used _
    (halts.haltsWithin_of_no_randomBit BinaryProductProgram.no_randomBit)
    (BinaryProductProgram.haltsWithin input)).symm.trans
      (halts.evalWithin_eq_pure_of_no_randomBit BinaryProductProgram.no_randomBit)

end Machine.BinaryProductSemantics
