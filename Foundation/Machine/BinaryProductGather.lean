import Foundation.Machine.BinaryProductWorkspace

namespace Machine.BinaryProductGather

open BinaryProductSelection

private inductive Action where
  | skip | copy | zero
  deriving DecidableEq

/-- Each selected bit is copied by a write and a head movement. Even a
skipped track is traversed by native instructions; no matrix projection is
an instruction of the machine. -/
private def block (base nextPc : Nat) (action : Action) : Program :=
  [.branch .input 45 (base + 1) (base + 4),
   (if action = .skip then .jump (base + 2) else .write .output false),
   (if action = .skip then .jump (base + 3) else .moveRight .output),
   .jump (base + 7),
   (match action with
    | .skip => .jump (base + 5)
    | .copy => .write .output true
    | .zero => .write .output false),
   (if action = .skip then .jump (base + 6) else .moveRight .output),
   .jump (base + 7), .moveRight .input, .jump nextPc]

private def nextPc (index : Nat) : Nat := if index = 4 then 0 else 9 * (index + 1)
private def code (actions : Nat → Action) : Program :=
  block 0 9 (actions 0) ++ block 9 18 (actions 1) ++
  block 18 27 (actions 2) ++ block 27 36 (actions 3) ++
  block 36 0 (actions 4) ++ [.halt]

private theorem lookup (actions : Nat → Action) (index offset : Nat)
    (hIndex : index < 5) (hOffset : offset < 9) :
    (code actions)[9 * index + offset]? =
      (block (9 * index) (nextPc index) (actions index))[offset]? := by
  interval_cases index <;> interval_cases offset <;> simp [code, block, nextPc]

private def emitted : Action → Bool → List Bool
  | .skip, _ => []
  | .copy, bit => [bit]
  | .zero, _ => [false]

private def successor (index : Nat) : Nat := if index = 4 then 0 else index + 1

private def project (actions : Nat → Action) (index : Nat) : List Bool → List Bool
  | [] => []
  | bit :: rest => emitted (actions index) bit ++ project actions (successor index) rest

private def state (index : Nat) (before written : List (Option Bool)) (input : List Bool) : Configuration :=
  { pc := 9 * index, inputTape := { Tape.ofBits input with left := before },
    outputTape := { left := written } }

private def finish (before written : List (Option Bool)) : Configuration :=
  { pc := 45, inputTape := { left := before }, outputTape := { left := written }, halted := true }

set_option maxHeartbeats 800000 in
private theorem eval_bit (actions : Nat → Action) (index : Nat) (hIndex : index < 5)
    (before written : List (Option Bool)) (bit : Bool) (rest : List Bool) :
    evalConfigWithin (code actions) (state index before written (bit :: rest)) 6 =
      PMF.pure (state (successor index) (some bit :: before)
        ((emitted (actions index) bit).reverse.map some ++ written) rest) := by
  have h0 := lookup actions index 0 hIndex (by omega)
  have h1 := lookup actions index 1 hIndex (by omega)
  have h2 := lookup actions index 2 hIndex (by omega)
  have h3 := lookup actions index 3 hIndex (by omega)
  have h4 := lookup actions index 4 hIndex (by omega)
  have h5 := lookup actions index 5 hIndex (by omega)
  have h6 := lookup actions index 6 hIndex (by omega)
  have h7 := lookup actions index 7 hIndex (by omega)
  have h8 := lookup actions index 8 hIndex (by omega)
  simp only [Nat.add_zero, block, List.getElem?_cons_zero, List.getElem?_cons_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  cases hAction : actions index <;> cases bit <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, state, successor, nextPc, emitted, hAction,
      h0, h1, h2, h3, h4, h5, h6, h7, h8,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write, PMF.pure_bind]

private theorem eval_end (actions : Nat → Action) (index : Nat) (hIndex : index < 5)
    (before written : List (Option Bool)) :
    evalConfigWithin (code actions) (state index before written []) 2 =
      PMF.pure (finish before written) := by
  have h0 := lookup actions index 0 hIndex (by omega)
  have hEnd : (code actions)[45]? = some .halt := by simp [code, block]
  simp [evalConfigWithin, stepPMF, next, state, finish, hEnd,
    show (code actions)[9 * index]? = some (.branch .input 45 (9 * index + 1) (9 * index + 4)) by
      simpa [block] using h0,
    Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]

private theorem eval_bits (actions : Nat → Action) (index : Nat) (hIndex : index < 5)
    (before written : List (Option Bool)) (input : List Bool) :
    evalConfigWithin (code actions) (state index before written input) (6 * input.length + 2) =
      PMF.pure (finish (input.reverse.map some ++ before)
        ((project actions index input).reverse.map some ++ written)) := by
  induction input generalizing index before written with
  | nil => simpa [project] using eval_end actions index hIndex before written
  | cons bit rest ih =>
      have hNext : successor index < 5 := by unfold successor; split <;> omega
      have hBudget : 6 * (bit :: rest).length + 2 = 6 + (6 * rest.length + 2) := by simp; omega
      rw [hBudget, evalConfigWithin_add, eval_bit actions index hIndex, PMF.pure_bind]
      simpa [project, List.reverse_cons, List.reverse_append, List.map_append, List.append_assoc] using
        ih (successor index) hNext (some bit :: before)
          ((emitted (actions index) bit).reverse.map some ++ written)

private theorem eval_project (actions : Nat → Action) (input : List Bool) :
    evalWithin (code actions) input (6 * input.length + 2) =
      PMF.pure (some (project actions 0 input)) := by
  have hInitial : Configuration.initial input = state 0 [] [] input := by cases input <;> rfl
  rw [evalWithin, hInitial, eval_bits actions 0 (by omega), PMF.pure_map]
  simp [finish, Configuration.outputBits, Tape.bits]

private theorem halts (actions : Nat → Action) (input : List Bool) :
    HaltsWithin (code actions) input (6 * (input.length + 1)) := by
  have hInitial : Configuration.initial input = state 0 [] [] input := by cases input <;> rfl
  have hBudget : 6 * (input.length + 1) = (6 * input.length + 2) + 4 := by omega
  intro result run
  have hSupport := (mem_support_evalConfigWithin_iff (code actions) _ result _).mpr run
  rw [hInitial, hBudget, evalConfigWithin_add, eval_bits actions 0 (by omega), PMF.pure_bind] at hSupport
  have hHalted (c : Configuration) (steps : Nat) (h : c.halted = true) :
      evalConfigWithin (code actions) c steps = PMF.pure c := by
    induction steps with
    | zero => rfl
    | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]
  rw [hHalted _ _ rfl, PMF.mem_support_pure_iff] at hSupport
  exact hSupport ▸ rfl

private theorem polynomial (actions : Nat → Action) : PolynomialTime (code actions) :=
  ⟨fun length => 6 * (length + 1),
    (PolynomiallyBounded.const 6).mul (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)),
    halts actions⟩

private def doubleActions : Nat → Action
  | 0 | 2 => .copy
  | _ => .skip

private def addActions (selected : Bool) : Nat → Action
  | 0 | 2 => .copy
  | 1 => if selected then .copy else .zero
  | _ => .skip

private def resultActions : Nat → Action
  | 0 => .copy
  | _ => .skip

/-- Gather accumulator/modulus pairs. The caller supplies the double
kernel's header with separate native instructions. -/
def doublePairsProgram : Program := code doubleActions
/-- Gather accumulator/selected operand/modulus triples. A zero multiplier
bit writes zero operand bits; it does not omit or resize the operand track. -/
def addTriplesProgram (selected : Bool) : Program := code (addActions selected)
/-- Copy the final accumulator track into a contiguous result block. -/
def resultProgram : Program := code resultActions

private theorem project_matrix (actions : Nat → Action) (columns : List Column) :
    project actions 0 (matrix columns) = columns.flatMap (fun column =>
      emitted (actions 0) column.accumulator ++ emitted (actions 1) column.operand ++
      emitted (actions 2) column.modulus ++ emitted (actions 3) column.multiplier ++
      emitted (actions 4) column.pending) := by
  induction columns with
  | nil => rfl
  | cons column rest ih =>
      rw [show matrix (column :: rest) = row column ++ matrix rest from rfl]
      simp only [List.flatMap_cons, row, List.cons_append, project, successor,
        ↓reduceIte, Nat.reduceAdd, Nat.reduceEqDiff, List.nil_append]
      rw [ih]
      simp [List.append_assoc]

private theorem pairs_flatMap (columns : List Column) :
    BinaryComparison.interleave (columns.map fun column => (column.accumulator, column.modulus)) =
      columns.flatMap (fun column => [column.accumulator, column.modulus]) := by
  induction columns with
  | nil => rfl
  | cons column rest ih => simp [BinaryComparison.interleave, ih]

private theorem triples_flatMap (selected : Bool) (columns : List Column) :
    BinaryModularAddition.interleave (columns.map fun column =>
      ((column.accumulator, if selected then column.operand else false), column.modulus)) =
      columns.flatMap (fun column =>
        [column.accumulator, if selected then column.operand else false, column.modulus]) := by
  induction columns with
  | nil => rfl
  | cons column rest ih => simp only [BinaryModularAddition.interleave, List.map_cons, List.flatMap_cons, ih, List.cons_append, List.nil_append]

private theorem results_flatMap (columns : List Column) :
    columns.flatMap (fun column => [column.accumulator]) = columns.map Column.accumulator := by
  induction columns with
  | nil => rfl
  | cons column rest ih => simp [ih]

theorem eval_doublePairs (columns : List Column) :
    evalWithin doublePairsProgram (matrix columns) (30 * columns.length + 2) =
      PMF.pure (some (BinaryComparison.interleave
        (columns.map fun column => (column.accumulator, column.modulus)))) := by
  have hLength : (matrix columns).length = 5 * columns.length := by simp [matrix, row]; omega
  simpa [doublePairsProgram, hLength, project_matrix, doubleActions, emitted,
    pairs_flatMap, ← Nat.mul_assoc] using
    eval_project doubleActions (matrix columns)

set_option maxHeartbeats 800000 in
theorem eval_addTriples (selected : Bool) (columns : List Column) :
    evalWithin (addTriplesProgram selected) (matrix columns) (30 * columns.length + 2) =
      PMF.pure (some (BinaryModularAddition.interleave
        (columns.map fun column => ((column.accumulator, if selected then column.operand else false), column.modulus)))) := by
  have hLength : (matrix columns).length = 5 * columns.length := by simp [matrix, row]; omega
  have h := eval_project (addActions selected) (matrix columns)
  rw [triples_flatMap]
  cases selected <;>
    simpa [addTriplesProgram, hLength, project_matrix, addActions, emitted,
      ← Nat.mul_assoc] using h

theorem eval_result (columns : List Column) :
    evalWithin resultProgram (matrix columns) (30 * columns.length + 2) =
      PMF.pure (some (columns.map Column.accumulator)) := by
  have hLength : (matrix columns).length = 5 * columns.length := by simp [matrix, row]; omega
  simpa [resultProgram, hLength, project_matrix, resultActions, emitted, ← Nat.mul_assoc, results_flatMap] using
    eval_project resultActions (matrix columns)

theorem doublePairs_polynomialTime : PolynomialTime doublePairsProgram := polynomial doubleActions
theorem addTriples_polynomialTime (selected : Bool) : PolynomialTime (addTriplesProgram selected) := polynomial (addActions selected)
theorem result_polynomialTime : PolynomialTime resultProgram := polynomial resultActions

/-- Both tape heads start at the first input cell / first free result cell.
The prefixes are retained physical cells, not data reloaded by a wrapper. -/
def gatherStart (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits input with left := beforeInput }, outputTape := { left := beforeOutput } }

/-- Both scans end just beyond their contiguous blocks. The source matrix
and the caller's prefixes survive the arithmetic-input preparation. -/
def gatherFinish (beforeInput beforeOutput : List (Option Bool))
    (input output : List Bool) : Configuration :=
  { pc := 45, inputTape := { left := input.reverse.map some ++ beforeInput },
    outputTape := { left := output.reverse.map some ++ beforeOutput }, halted := true }

theorem eval_doublePairs_context (columns : List Column)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin doublePairsProgram (gatherStart beforeInput beforeOutput (matrix columns))
      (30 * columns.length + 2) =
      PMF.pure (gatherFinish beforeInput beforeOutput (matrix columns)
        (BinaryComparison.interleave (columns.map fun column => (column.accumulator, column.modulus)))) := by
  have hLength : (matrix columns).length = 5 * columns.length := by simp [matrix, row]; omega
  simpa [doublePairsProgram, gatherStart, gatherFinish, state, finish, hLength,
    project_matrix, doubleActions, emitted, pairs_flatMap, ← Nat.mul_assoc] using
    eval_bits doubleActions 0 (by omega) beforeInput beforeOutput (matrix columns)

set_option maxHeartbeats 800000 in
theorem eval_addTriples_context (selected : Bool) (columns : List Column)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin (addTriplesProgram selected) (gatherStart beforeInput beforeOutput (matrix columns))
      (30 * columns.length + 2) =
      PMF.pure (gatherFinish beforeInput beforeOutput (matrix columns)
        (BinaryModularAddition.interleave (columns.map fun column =>
          ((column.accumulator, if selected then column.operand else false), column.modulus)))) := by
  have hLength : (matrix columns).length = 5 * columns.length := by simp [matrix, row]; omega
  have h := eval_bits (addActions selected) 0 (by omega) beforeInput beforeOutput (matrix columns)
  rw [triples_flatMap]
  cases selected <;>
    simpa [addTriplesProgram, gatherStart, gatherFinish, state, finish, hLength,
      project_matrix, addActions, emitted, ← Nat.mul_assoc] using h

theorem eval_result_context (columns : List Column)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin resultProgram (gatherStart beforeInput beforeOutput (matrix columns))
      (30 * columns.length + 2) =
      PMF.pure (gatherFinish beforeInput beforeOutput (matrix columns) (columns.map Column.accumulator)) := by
  have hLength : (matrix columns).length = 5 * columns.length := by simp [matrix, row]; omega
  simpa [resultProgram, gatherStart, gatherFinish, state, finish, hLength,
    project_matrix, resultActions, emitted, results_flatMap, ← Nat.mul_assoc] using
    eval_bits resultActions 0 (by omega) beforeInput beforeOutput (matrix columns)

private theorem halts_exact (actions : Nat → Action) (input : List Bool)
    (beforeInput beforeOutput : List (Option Bool))
    (result : Configuration)
    (run : PaddedRunsFor (code actions) (state 0 beforeInput beforeOutput input) result
      (6 * input.length + 2)) : result.halted = true := by
  have hSupport := (mem_support_evalConfigWithin_iff (code actions) _ result _).mpr run
  rw [eval_bits actions 0 (by omega), PMF.mem_support_pure_iff] at hSupport
  exact hSupport ▸ rfl

/-- Contextual stopping for each gather code, retaining arbitrary saved
prefixes and charging every scan step on malformed rows as well. -/
theorem doublePairs_haltsFrom (input : List Bool) (beforeInput beforeOutput : List (Option Bool))
    (result : Configuration)
    (run : PaddedRunsFor doublePairsProgram (gatherStart beforeInput beforeOutput input) result
      (6 * input.length + 2)) : result.halted = true :=
  halts_exact doubleActions input beforeInput beforeOutput result run

theorem addTriples_haltsFrom (selected : Bool) (input : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) (result : Configuration)
    (run : PaddedRunsFor (addTriplesProgram selected) (gatherStart beforeInput beforeOutput input) result
      (6 * input.length + 2)) : result.halted = true :=
  halts_exact (addActions selected) input beforeInput beforeOutput result run

theorem result_haltsFrom (input : List Bool) (beforeInput beforeOutput : List (Option Bool))
    (result : Configuration)
    (run : PaddedRunsFor resultProgram (gatherStart beforeInput beforeOutput input) result
      (6 * input.length + 2)) : result.halted = true :=
  halts_exact resultActions input beforeInput beforeOutput result run

private def header : Program := [.write .output false, .moveRight .output]

/-- Preparation for the doubling kernel includes an actual write of its
zero header, followed by the native matrix scan. The subroutine return and
the final halt are both charged transitions. -/
def doubleInputProgram : Program :=
  Program.withSubroutine header doublePairsProgram [.halt] 49

private theorem eval_header (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    evalConfigWithin doubleInputProgram (gatherStart beforeInput beforeOutput input) 2 =
      PMF.pure ((state 0 beforeInput (some false :: beforeOutput) input).rebasePc 2) := by
  cases input <;>
    simp [evalConfigWithin, stepPMF, next, doubleInputProgram, header, Program.withSubroutine,
      gatherStart, state, Configuration.rebasePc, Instruction.next, Configuration.advance,
      Configuration.updateTape, Tape.write, Tape.moveRight, PMF.pure_bind]

private theorem eval_doubleInput_raw (beforeInput beforeOutput : List (Option Bool)) (input : List Bool) :
    evalConfigWithin doubleInputProgram (gatherStart beforeInput beforeOutput input)
      (6 * input.length + 5) =
      PMF.pure { gatherFinish beforeInput beforeOutput input (false :: project doubleActions 0 input) with pc := 49 } := by
  have hCall := Program.evalConfigWithin_withSubroutine_final_halt header doublePairsProgram
    (state 0 beforeInput (some false :: beforeOutput) input)
    (by change 0 ≤ doublePairsProgram.length; omega) rfl (6 * input.length + 2)
    (halts_exact doubleActions input beforeInput (some false :: beforeOutput))
  have hLength : doublePairsProgram.length = 46 := by simp [doublePairsProgram, code, block]
  simp only [show header.length = 2 from rfl, hLength] at hCall
  change evalConfigWithin doubleInputProgram
    ((state 0 beforeInput (some false :: beforeOutput) input).rebasePc 2)
    (6 * input.length + 2 + 1) = _ at hCall
  rw [show 6 * input.length + 5 = 2 + (6 * input.length + 2 + 1) by omega,
    evalConfigWithin_add, eval_header, PMF.pure_bind, hCall]
  change (evalConfigWithin (code doubleActions)
    (state 0 beforeInput (some false :: beforeOutput) input) (6 * input.length + 2)).map _ = _
  rw [eval_bits doubleActions 0 (by omega), PMF.pure_map]
  simp [finish, gatherFinish, List.reverse_cons, List.map_append, List.append_assoc]

theorem eval_doubleInput_context (columns : List Column)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin doubleInputProgram (gatherStart beforeInput beforeOutput (matrix columns))
      (30 * columns.length + 5) =
      PMF.pure { gatherFinish beforeInput beforeOutput (matrix columns)
        (false :: BinaryComparison.interleave
          (columns.map fun column => (column.accumulator, column.modulus))) with pc := 49 } := by
  have hLength : (matrix columns).length = 5 * columns.length := by simp [matrix, row]; omega
  simpa [hLength, project_matrix, doubleActions, emitted, pairs_flatMap, ← Nat.mul_assoc] using
    eval_doubleInput_raw beforeInput beforeOutput (matrix columns)

theorem eval_doubleInput (columns : List Column) :
    evalWithin doubleInputProgram (matrix columns) (30 * columns.length + 5) =
      PMF.pure (some (false :: BinaryComparison.interleave
        (columns.map fun column => (column.accumulator, column.modulus)))) := by
  have hInitial : Configuration.initial (matrix columns) = gatherStart [] [] (matrix columns) := by
    cases matrix columns <;> rfl
  rw [evalWithin, hInitial, eval_doubleInput_context, PMF.pure_map]
  simp [gatherFinish, Configuration.outputBits, Tape.bits]

theorem doubleInput_haltsFrom (input : List Bool) (beforeInput beforeOutput : List (Option Bool))
    (result : Configuration)
    (run : PaddedRunsFor doubleInputProgram (gatherStart beforeInput beforeOutput input) result
      (6 * input.length + 5)) : result.halted = true := by
  have hSupport := (mem_support_evalConfigWithin_iff doubleInputProgram _ result _).mpr run
  rw [eval_doubleInput_raw, PMF.mem_support_pure_iff] at hSupport
  exact hSupport ▸ rfl

theorem doubleInput_haltsWithin (input : List Bool) :
    HaltsWithin doubleInputProgram input (6 * (input.length + 1)) := by
  have hInitial : Configuration.initial input = gatherStart [] [] input := by cases input <;> rfl
  intro result run
  have hSupport := (mem_support_evalConfigWithin_iff doubleInputProgram _ result _).mpr run
  have hBudget : 6 * (input.length + 1) = (6 * input.length + 5) + 1 := by omega
  rw [hInitial, hBudget, evalConfigWithin_add, eval_doubleInput_raw, PMF.pure_bind] at hSupport
  simp [evalConfigWithin, stepPMF, next, gatherFinish] at hSupport
  exact hSupport ▸ rfl

theorem doubleInput_polynomialTime : PolynomialTime doubleInputProgram :=
  ⟨fun length => 6 * (length + 1),
    (PolynomiallyBounded.const 6).mul (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)),
    doubleInput_haltsWithin⟩

theorem doubleInput_no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ doubleInputProgram := by
  cases tape <;> decide

theorem addTriples_no_randomBit (selected : Bool) (tape : TapeId) :
    Instruction.randomBit tape ∉ addTriplesProgram selected := by
  cases selected <;> cases tape <;> decide

end Machine.BinaryProductGather
