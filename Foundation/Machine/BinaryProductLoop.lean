import Foundation.Machine.BinaryProductPhase

set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace Machine.BinaryProductLoop

open BinaryProductSelection BinaryProductWorkspace

private def selectCode : Program := BinaryProductSelection.program.asSubroutine 0 20
private def bodyLength (bit : Bool) : Nat :=
  1 + BinaryProductPhase.doubleProgram.length + 1 +
    (BinaryProductPhase.addProgram bit).length + 1 + 1
private def doubleReturn (base : Nat) : Nat :=
  base + 1 + BinaryProductPhase.doubleProgram.length + 1
private def addReturn (base : Nat) (bit : Bool) : Nat :=
  doubleReturn base + (BinaryProductPhase.addProgram bit).length + 1
private def body (base : Nat) (bit : Bool) : Program :=
  [.erase .output] ++ BinaryProductPhase.doubleProgram.asSubroutine (base + 1) (doubleReturn base) ++
    (BinaryProductPhase.addProgram bit).asSubroutine (doubleReturn base) (addReturn base bit) ++ [.jump 3]
private def header : Program :=
  [.branch .output 21 22 (22 + bodyLength false), .halt]

/-- One fixed native loop for arbitrary complete five-track matrices. The
finite branch selects one of two finite arithmetic bodies; it does not
evaluate a Boolean or a natural-number operation outside the machine.
Each body clears the selected output bit, invokes doubling and addition on
the retained matrix, and jumps back to the pending-flag selector. -/
def program : Program :=
  selectCode ++ header ++ body 22 false ++ body (22 + bodyLength false) true

theorem entry_in_range : 3 ≤ program.length := by
  simp only [program, selectCode, List.length_append, Program.asSubroutine_length,
    show BinaryProductSelection.program.length = 19 from rfl]
  omega

private def beforeBody (bit : Bool) : Program :=
  selectCode ++ header ++ if bit then body 22 false else []
private def bodyBase (bit : Bool) : Nat := if bit then 22 + bodyLength false else 22
private def afterBody (bit : Bool) : Program :=
  if bit then [] else body (22 + bodyLength false) true
private def beforeDouble (bit : Bool) : Program := beforeBody bit ++ [.erase .output]
private def beforeAdd (bit : Bool) : Program :=
  beforeDouble bit ++ BinaryProductPhase.doubleProgram.asSubroutine
    (bodyBase bit + 1) (doubleReturn (bodyBase bit))
private def doubleSuffix (bit : Bool) : Program :=
  (BinaryProductPhase.addProgram bit).asSubroutine (doubleReturn (bodyBase bit))
    (addReturn (bodyBase bit) bit) ++ [.jump 3] ++ afterBody bit
private def addSuffix (bit : Bool) : Program := [.jump 3] ++ afterBody bit

private theorem body_length (base : Nat) (bit : Bool) : (body base bit).length = bodyLength bit := by
  simp [body, bodyLength, Nat.add_assoc]; omega
private theorem beforeBody_length (bit : Bool) : (beforeBody bit).length = bodyBase bit := by
  cases bit <;> simp [beforeBody, selectCode, header, bodyBase, body_length,
    show BinaryProductSelection.program.length = 19 from rfl] <;> omega
private theorem beforeDouble_length (bit : Bool) :
    (beforeDouble bit).length = bodyBase bit + 1 := by
  simp [beforeDouble, beforeBody_length]
private theorem beforeAdd_length (bit : Bool) :
    (beforeAdd bit).length = doubleReturn (bodyBase bit) := by
  simp [beforeAdd, beforeDouble_length, doubleReturn, Nat.add_assoc]

private theorem selection_layout : program = Program.withSubroutine [] BinaryProductSelection.program
    (header ++ body 22 false ++ body (22 + bodyLength false) true) 20 := by
  simp [program, selectCode, Program.withSubroutine, List.append_assoc]
private theorem double_layout (bit : Bool) : program =
    Program.withSubroutine (beforeDouble bit) BinaryProductPhase.doubleProgram
      (doubleSuffix bit) (doubleReturn (bodyBase bit)) := by
  simp only [Program.withSubroutine, beforeDouble_length]
  cases bit <;> simp [program, beforeDouble, beforeBody, doubleSuffix, afterBody,
    bodyBase, body, List.append_assoc]
private theorem add_layout (bit : Bool) : program =
    Program.withSubroutine (beforeAdd bit) (BinaryProductPhase.addProgram bit)
      (addSuffix bit) (addReturn (bodyBase bit) bit) := by
  simp only [Program.withSubroutine, beforeAdd_length]
  cases bit <;> simp [program, beforeAdd, beforeDouble, beforeBody, addSuffix,
    afterBody, bodyBase, body, List.append_assoc]

private theorem branch_lookup : program[20]? = some
    (.branch .output 21 22 (22 + bodyLength false)) := by
  rw [selection_layout]
  have lookup := Program.withSubroutine_getElem?_suffix [] BinaryProductSelection.program
    (header ++ body 22 false ++ body (22 + bodyLength false) true) 20 0
  simpa only [List.length_nil, show BinaryProductSelection.program.length = 19 from rfl,
    Nat.zero_add, header, List.cons_append, List.getElem?_cons_zero] using lookup

private theorem halt_lookup : program[21]? = some .halt := by
  rw [selection_layout]
  have lookup := Program.withSubroutine_getElem?_suffix [] BinaryProductSelection.program
    (header ++ body 22 false ++ body (22 + bodyLength false) true) 20 1
  simpa only [List.length_nil, show BinaryProductSelection.program.length = 19 from rfl,
    Nat.zero_add, header, List.cons_append, List.getElem?_cons_succ, List.getElem?_cons_zero] using lookup

private theorem erase_lookup (bit : Bool) : program[bodyBase bit]? = some (.erase .output) := by
  rw [double_layout bit]
  rw [Program.withSubroutine_getElem?_pre _ _ _ _ _ (by rw [beforeDouble_length]; omega)]
  simp only [beforeDouble]
  rw [List.getElem?_append_right (by rw [beforeBody_length])]
  simp only [beforeBody_length, Nat.sub_self, List.getElem?_cons_zero]

private theorem jump_lookup (bit : Bool) : program[addReturn (bodyBase bit) bit]? = some (.jump 3) := by
  rw [add_layout bit]
  have lookup := Program.withSubroutine_getElem?_suffix (beforeAdd bit)
    (BinaryProductPhase.addProgram bit) (addSuffix bit) (addReturn (bodyBase bit) bit) 0
  change _ = some (Instruction.jump 3) at lookup
  simpa only [beforeAdd_length, addReturn, Nat.add_zero] using lookup

private theorem body_no_randomBit (base : Nat) (bit : Bool) (tape : TapeId) :
    Instruction.randomBit tape ∉ body base bit := by
  simp only [body, List.mem_append, not_or]
  refine ⟨⟨⟨by simp, ?_⟩, ?_⟩, by simp⟩
  · exact Program.asSubroutine_no_randomBit _
      (BinaryProductPhase.no_randomBit _ _ BinaryProductGather.doubleInput_no_randomBit
        BinaryDoubleReduction.no_randomBit) _ _ tape
  · exact Program.asSubroutine_no_randomBit _
      (BinaryProductPhase.no_randomBit _ _ (BinaryProductGather.addTriples_no_randomBit bit)
        BinaryModularAddition.no_randomBit) _ _ tape

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  simp only [program, List.mem_append, not_or]
  exact ⟨⟨⟨Program.asSubroutine_no_randomBit _ BinaryProductSelection.no_randomBit 0 20 tape,
    by simp [header]⟩, body_no_randomBit _ _ tape⟩, body_no_randomBit _ _ tape⟩

def start (columns : List Column) (saved : List (Option Bool)) : Configuration :=
  BinaryProductSelection.selectionFromEnd columns saved

def iterationBudget (width : Nat) : Nat :=
  7 * width + 3 + 1 + 1 + BinaryProductPhase.doubleBudget width +
    BinaryProductPhase.addBudget width + 1

private theorem left_blank (bits : List Bool) :
    ({ left := bits.map some ++ [none] } : Tape).Equivalent { left := bits.map some } := by
  refine ⟨rfl, ?_, fun _ => rfl⟩
  intro index
  induction bits generalizing index with
  | nil => cases index <;> simp
  | cons bit rest ih =>
      cases index with
      | zero => rfl
      | succ index => simpa only [List.map_cons, List.cons_append, List.getD_cons_succ] using ih index

private theorem replaceAccumulator_length (columns : List Column) (bits : List Bool)
    (hLength : bits.length = columns.length) :
    (replaceAccumulator columns bits).length = columns.length := by
  simp [replaceAccumulator, hLength]

/-- Every successful native iteration consumes exactly one flag. The two
arithmetic calls reuse the same matrix and preserve all remaining flags.
No assumption on the numeric modulus or operands is needed for this step
count and workspace statement. -/
theorem iteration (columns : List Column) (saved : List (Option Bool)) (bit : Bool)
    (hSelected : selected columns.reverse = some bit) :
    ∃ (nextColumns : List Column) (nextSaved : List (Option Bool))
      (target : Configuration) (used : Nat),
      nextColumns.length = columns.length ∧
      pendingCount nextColumns = pendingCount columns - 1 ∧
      used ≤ iterationBudget columns.length ∧
      RunsFor program (start columns saved) target used ∧
      target.Equivalent (start nextColumns nextSaved) ∧
      ∃ (doubleBits addBits : List Bool),
        doubleBits.length = columns.length ∧ addBits.length = columns.length ∧
        nextColumns = replaceAccumulator
          (replaceAccumulator (consume columns.reverse).reverse doubleBits) addBits ∧
        evalWithin BinaryDoubleReduction.program
          (BinaryProductPhase.doubleRequest (consume columns.reverse).reverse)
          (18 * columns.length + 15) = PMF.pure (some doubleBits) ∧
        evalWithin BinaryModularAddition.program
          (BinaryProductPhase.addRequest bit (replaceAccumulator (consume columns.reverse).reverse doubleBits))
          (24 * columns.length + 10) = PMF.pure (some addBits) := by
  let chosen : Configuration :=
    { selectionFinish columns with outputTape := { left := saved, current := some bit } }
  have hChosen : chosen.halted = true := selectionFinish_halted columns
  have selectionEval : evalConfigWithin BinaryProductSelection.program
      (selectionFromEnd columns saved) (7 * columns.length + 3) = PMF.pure chosen := by
    simpa only [selectionFinish_outputTape, hSelected] using eval_selection_from_end columns saved
  obtain ⟨s1, u1, hu1, r1, e1⟩ := nativeCall_of_eval [] BinaryProductSelection.program
    (header ++ body 22 false ++ body (22 + bodyLength false) true) 20
    (selectionFromEnd columns saved) chosen (start columns saved) (7 * columns.length + 3)
    (by change 3 ≤ 19; omega) rfl hChosen selectionEval (Configuration.Equivalent.refl _)
  rw [← selection_layout] at r1
  let branched : Configuration := { s1 with pc := bodyBase bit }
  have branchStep : Step program s1 branched := by
    have hp : s1.pc = 20 := e1.1.symm
    have ha : s1.halted = false := e1.2.1.symm
    have hc : s1.outputTape.current = some bit := e1.2.2.2.1.symm
    cases bit <;> simp [Step, successors, next, hp, ha, branch_lookup,
      branched, Instruction.next, Configuration.tape, hc, bodyBase]
  let erased : Configuration :=
    { branched with pc := bodyBase bit + 1, outputTape := branched.outputTape.write none }
  have eraseStep : Step program branched erased := by
    have ha : s1.halted = false := e1.2.1.symm
    simp [Step, successors, next, branched, ha, erase_lookup, erased,
      Instruction.next, Configuration.advance, Configuration.updateTape]
  let consumed := (consume columns.reverse).reverse
  have hConsumed : consumed.length = columns.length := by
    simp [consumed, consume_length]
  obtain ⟨leading, remaining, hMatrix, hSplit⟩ := selectionFinish_chosen_split columns bit hSelected
  obtain ⟨doubleBits, doubled, doubleSteps, doubleSaved, hDoubleLength, hDoubleBound,
      doubleRun, hDoubleHalt, hDoubleInput, hDoubleOutput, hDoubleCorrect⟩ :=
    BinaryProductPhase.double_runs_from_split consumed leading remaining saved hMatrix
  let doubleStart : Configuration :=
    { inputTape := { Tape.ofBits remaining with left := leading.reverse.map some },
      outputTape := { left := saved } }
  have hDoubleLayout : (doubleStart.rebasePc (beforeDouble bit).length).Equivalent erased := by
    refine ⟨?_, e1.2.1, ?_, ?_⟩
    · rw [beforeDouble_length]; rfl
    · exact hSplit.symm.trans e1.2.2.1
    · exact e1.2.2.2.write none
  obtain ⟨u2, hu2, embeddedDouble⟩ := doubleRun.withSubroutine_halted
    (beforeDouble bit) BinaryProductPhase.doubleProgram (doubleSuffix bit)
    (doubleReturn (bodyBase bit)) (by change 0 ≤ _; omega) rfl hDoubleHalt
  obtain ⟨s2, r2, e2⟩ := embeddedDouble.exists_equivalent hDoubleLayout
  rw [← double_layout bit] at r2
  let intermediate := replaceAccumulator consumed doubleBits
  have hIntermediate : intermediate.length = columns.length :=
    (replaceAccumulator_length consumed doubleBits hDoubleLength).trans hConsumed
  let intermediateSaved := doubleBits.reverse.map some ++ none :: doubleSaved
  obtain ⟨addBits, added, addSteps, addSaved, hAddLength, hAddBound,
      addRun, hAddHalt, hAddInput, hAddOutput, hAddCorrect⟩ :=
    BinaryProductPhase.add_runs bit intermediate intermediateSaved
  have hAddLayout : ((BinaryProductPhase.start intermediate intermediateSaved).rebasePc
      (beforeAdd bit).length).Equivalent s2 := by
    refine ⟨?_, e2.2.1, ?_, ?_⟩
    · change (beforeAdd bit).length + 0 = s2.pc
      rw [beforeAdd_length, Nat.add_zero]
      exact e2.1
    · exact hDoubleInput.symm.trans e2.2.2.1
    · exact hDoubleOutput.symm.trans e2.2.2.2
  obtain ⟨u3, hu3, embeddedAdd⟩ := addRun.withSubroutine_halted
    (beforeAdd bit) (BinaryProductPhase.addProgram bit) (addSuffix bit)
    (addReturn (bodyBase bit) bit) (by change 0 ≤ _; omega) rfl hAddHalt
  obtain ⟨s3, r3, e3⟩ := embeddedAdd.exists_equivalent hAddLayout
  rw [← add_layout bit] at r3
  let nextColumns := replaceAccumulator intermediate addBits
  let nextSaved := addBits.reverse.map some ++ none :: addSaved
  let target : Configuration := { s3 with pc := 3 }
  have jumpStep : Step program s3 target := by
    have hp : s3.pc = addReturn (bodyBase bit) bit := e3.1.symm
    have ha : s3.halted = false := e3.2.1.symm
    simp [Step, successors, next, hp, ha, jump_lookup, Instruction.next, target]
  have native := (((r1.succ branchStep).succ eraseStep).trans r2).trans r3 |>.succ jumpStep
  refine ⟨nextColumns, nextSaved, target, u1 + 1 + 1 + u2 + u3 + 1, ?_, ?_, ?_, native, ?_, ?_⟩
  · exact (replaceAccumulator_length intermediate addBits hAddLength).trans hIntermediate
  · rw [replaceAccumulator_pendingCount _ _ hAddLength,
      replaceAccumulator_pendingCount _ _ hDoubleLength]
    simp [consumed, pendingCount_reverse, pendingCount_consume_eq_sub]
  · rw [hConsumed] at hDoubleBound
    rw [hIntermediate] at hAddBound
    dsimp only [iterationBudget]
    omega
  · refine ⟨rfl, e3.2.1.symm, ?_, ?_⟩
    · exact (e3.2.2.1.symm.trans hAddInput).trans (left_blank (matrix nextColumns).reverse)
    · exact e3.2.2.2.symm.trans hAddOutput
  · refine ⟨doubleBits, addBits, hDoubleLength.trans hConsumed, hAddLength.trans hIntermediate,
      rfl, ?_, ?_⟩
    · simpa only [hConsumed] using hDoubleCorrect
    · simpa only [hIntermediate] using hAddCorrect

theorem exhausted (columns : List Column) (saved : List (Option Bool))
    (hNone : selected columns.reverse = none) :
    ∃ (target : Configuration) (used : Nat), used ≤ 7 * columns.length + 5 ∧
      RunsFor program (start columns saved) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent { right := (matrix columns).map some ++ [none] } ∧
      target.outputTape.Equivalent { left := saved } := by
  let chosen : Configuration :=
    { selectionFinish columns with outputTape := { left := saved } }
  have hChosen : chosen.halted = true := selectionFinish_halted columns
  have selectionEval : evalConfigWithin BinaryProductSelection.program
      (selectionFromEnd columns saved) (7 * columns.length + 3) = PMF.pure chosen := by
    simpa only [selectionFinish_outputTape, hNone] using eval_selection_from_end columns saved
  obtain ⟨s1, used, hUsed, native, layout⟩ := nativeCall_of_eval [] BinaryProductSelection.program
    (header ++ body 22 false ++ body (22 + bodyLength false) true) 20
    (selectionFromEnd columns saved) chosen (start columns saved) (7 * columns.length + 3)
    (by change 3 ≤ 19; omega) rfl hChosen selectionEval (Configuration.Equivalent.refl _)
  rw [← selection_layout] at native
  let branched : Configuration := { s1 with pc := 21 }
  have hp : s1.pc = 20 := layout.1.symm
  have ha : s1.halted = false := layout.2.1.symm
  have hc : s1.outputTape.current = none := layout.2.2.2.1.symm
  have branchStep : Step program s1 branched := by
    simp [Step, successors, next, hp, ha, branch_lookup, Instruction.next,
      Configuration.tape, hc, branched]
  let target : Configuration := { branched with halted := true }
  have haltStep : Step program branched target := by
    simp [Step, successors, next, branched, ha, halt_lookup, Instruction.next, target]
  refine ⟨target, used + 1 + 1, by omega, (native.succ branchStep).succ haltStep, rfl, ?_, ?_⟩
  · have input := layout.2.2.1.symm
    simpa only [chosen, Configuration.resumeAt, selectionFinish_none_input columns hNone] using input
  · exact layout.2.2.2.symm

def budget (width pending : Nat) : Nat := (pending + 1) * (iterationBudget width + 3)

def widthBudget (width : Nat) : Nat := budget width width

theorem iterationBudget_polynomiallyBounded : PolynomiallyBounded iterationBudget :=
  (((((PolynomiallyBounded.const 7).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 3)).add (PolynomiallyBounded.const 1)).add
      (PolynomiallyBounded.const 1)).add BinaryProductPhase.doubleBudget_polynomiallyBounded
    |>.add BinaryProductPhase.addBudget_polynomiallyBounded |>.add (PolynomiallyBounded.const 1)

theorem widthBudget_polynomiallyBounded : PolynomiallyBounded widthBudget :=
  (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)).mul
    (iterationBudget_polynomiallyBounded.add (PolynomiallyBounded.const 3))

theorem widthBudget_le (width : Nat) : widthBudget width ≤ 297220 * (width + 1) ^ 4 := by
  have hDouble := BinaryProductPhase.doubleBudget_le width
  have hAdd := BinaryProductPhase.addBudget_le width
  have hIteration : iterationBudget width + 3 ≤ 297220 * (width + 1) ^ 3 := by
    dsimp only [iterationBudget]
    nlinarith [Nat.zero_le (width ^ 2), Nat.zero_le (width ^ 3)]
  calc
    widthBudget width ≤ (width + 1) * (297220 * (width + 1) ^ 3) :=
      Nat.mul_le_mul_left _ hIteration
    _ = 297220 * (width + 1) ^ 4 := by ring

/-- The complete native loop terminates on every complete matrix, including
numerically invalid operands. Selection consumes a stored flag on each
iteration, while both physical arithmetic phases preserve its remaining
flags and its width. The proof's natural-number induction is not an added
machine counter instruction. -/
theorem runs (columns : List Column) (saved : List (Option Bool)) :
    ∃ (finalColumns : List Column) (finalSaved : List (Option Bool))
      (target : Configuration) (used : Nat),
      finalColumns.length = columns.length ∧ pendingCount finalColumns = 0 ∧
      used ≤ budget columns.length (pendingCount columns) ∧
      RunsFor program (start columns saved) target used ∧ target.halted = true ∧
      target.inputTape.Equivalent { right := (matrix finalColumns).map some ++ [none] } ∧
      target.outputTape.Equivalent { left := finalSaved } := by
  have main (count : Nat) : ∀ (columns : List Column) (saved : List (Option Bool)),
      pendingCount columns = count →
      ∃ (finalColumns : List Column) (finalSaved : List (Option Bool))
        (target : Configuration) (used : Nat),
        finalColumns.length = columns.length ∧ pendingCount finalColumns = 0 ∧
        used ≤ budget columns.length count ∧
        RunsFor program (start columns saved) target used ∧ target.halted = true ∧
        target.inputTape.Equivalent { right := (matrix finalColumns).map some ++ [none] } ∧
        target.outputTape.Equivalent { left := finalSaved } := by
    induction count using Nat.strong_induction_on with
    | h count ih =>
        intro columns saved hCount
        cases hSelected : selected columns.reverse with
        | none =>
            have hZero : pendingCount columns = 0 := by
              simpa only [pendingCount_reverse] using (selected_none_iff _).mp hSelected
            obtain ⟨target, used, hUsed, native, hHalt, hInput, hOutput⟩ := exhausted columns saved hSelected
            refine ⟨columns, saved, target, used, rfl, hZero, ?_, native, hHalt, hInput, hOutput⟩
            dsimp only [budget, iterationBudget]
            have hc : count = 0 := hCount.symm.trans hZero
            rw [hc]
            omega
        | some bit =>
            have hPositive : 0 < pendingCount columns := by
              by_contra hNot
              have hZero : pendingCount columns.reverse = 0 := by rw [pendingCount_reverse]; omega
              have hNone := (selected_none_iff _).mpr hZero
              simp [hSelected] at hNone
            obtain ⟨nextColumns, nextSaved, middle, firstTime, hWidth, hPending, hFirst,
              firstRun, middleLayout, _⟩ := iteration columns saved bit hSelected
            have hLess : pendingCount nextColumns < count := by omega
            obtain ⟨finalColumns, finalSaved, canonical, lastTime, hFinalWidth, hFinalPending,
              hLast, lastRun, hHalt, hInput, hOutput⟩ := ih _ hLess nextColumns nextSaved rfl
            obtain ⟨target, actualLast, targetLayout⟩ := lastRun.exists_equivalent middleLayout.symm
            refine ⟨finalColumns, finalSaved, target, firstTime + lastTime,
              hFinalWidth.trans hWidth, hFinalPending, ?_, firstRun.trans actualLast, ?_, ?_, ?_⟩
            · rw [hWidth, hPending] at hLast
              have hc : pendingCount columns = (pendingCount columns - 1) + 1 := by omega
              calc
                firstTime + lastTime ≤ iterationBudget columns.length +
                    budget columns.length (pendingCount columns - 1) := Nat.add_le_add hFirst hLast
                _ ≤ budget columns.length count := by
                  rw [← hCount]
                  dsimp only [budget]
                  rw [← hc]
                  nlinarith
            · exact targetLayout.2.1.symm.trans hHalt
            · exact targetLayout.2.2.1.symm.trans hInput
            · exact targetLayout.2.2.2.symm.trans hOutput
  exact main _ columns saved rfl

theorem haltsFrom (columns : List Column) (saved : List (Option Bool)) :
    ∀ target, PaddedRunsFor program (start columns saved) target
      (budget columns.length (pendingCount columns)) → target.halted = true := by
  obtain ⟨_, _, target, used, _, _, hUsed, native, hHalt, _, _⟩ := runs columns saved
  exact native.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem haltsFrom_widthBudget (columns : List Column) (saved : List (Option Bool)) :
    ∀ target, PaddedRunsFor program (start columns saved) target
      (widthBudget columns.length) → target.halted = true := by
  obtain ⟨_, _, target, used, _, _, hUsed, native, hHalt, _, _⟩ := runs columns saved
  have hPending : pendingCount columns ≤ columns.length := List.length_filter_le _ _
  have hBound : budget columns.length (pendingCount columns) ≤ widthBudget columns.length :=
    Nat.mul_le_mul_right _ (Nat.add_le_add_right hPending 1)
  exact native.haltsFrom_of_no_randomBit hHalt no_randomBit (hUsed.trans hBound)

end Machine.BinaryProductLoop
