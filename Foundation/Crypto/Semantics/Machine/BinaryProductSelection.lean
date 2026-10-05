import Foundation.Crypto.Semantics.Machine.BinaryProductInitialization

namespace Machine.BinaryProductSelection

/-- Five actual tape bits form each work column. The flag is consumed by a
write instruction, not by an unbounded natural-number counter operation. -/
structure Column where
  accumulator : Bool
  operand : Bool
  modulus : Bool
  multiplier : Bool
  pending : Bool
  deriving DecidableEq

def row (column : Column) : List Bool :=
  [column.accumulator, column.operand, column.modulus, column.multiplier, column.pending]

def matrix (columns : List Column) : List Bool := columns.flatMap row

/-- Seek the right boundary, then move left by one five-bit column at a
time. The first pending flag encountered is cleared and its multiplier bit
is returned. Thus the highest unprocessed multiplier bit is selected. -/
def program : Program :=
  [.branch .input 3 1 1, .moveRight .input, .jump 0,
   .moveLeft .input, .branch .input 14 5 10,
   .moveLeft .input, .moveLeft .input, .moveLeft .input, .moveLeft .input, .jump 3,
   .write .input false, .moveLeft .input, .branch .input 14 15 17,
   .halt, .halt, .write .output false, .halt, .write .output true, .halt]

/-- The arguments are columns in reverse tape order. Only the first true
flag is modified; all other tracks and flags are preserved. -/
def consume : List Column → List Column
  | [] => []
  | column :: rest =>
      if column.pending then { column with pending := false } :: rest
      else column :: consume rest

def selected : List Column → Option Bool
  | [] => none
  | column :: rest => if column.pending then some column.multiplier else selected rest

def pendingCount (columns : List Column) : Nat :=
  (columns.filter fun column => column.pending).length

theorem pendingCount_reverse (columns : List Column) : pendingCount columns.reverse = pendingCount columns := by
  simp [pendingCount, List.filter_reverse]

private def seekState (before : List (Option Bool)) (bits : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits bits with left := before } }

private def selectState (before : List Bool) (current : Option Bool)
    (after : List (Option Bool)) : Configuration :=
  { pc := 3, inputTape := { left := before.map some, current := current, right := after } }

private theorem eval_seek_bit (bit : Bool) (before : List (Option Bool)) (rest : List Bool) :
    evalConfigWithin program (seekState before (bit :: rest)) 3 =
      PMF.pure (seekState (some bit :: before) rest) := by
  cases bit <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, program, seekState,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, PMF.pure_bind]

private theorem eval_seek_end (before : List Bool) :
    evalConfigWithin program (seekState (before.map some) []) 1 =
      PMF.pure (selectState before none []) := by
  simp [evalConfigWithin, stepPMF, next, program, seekState, selectState,
    Instruction.next, Configuration.tape, Tape.ofBits]

private theorem eval_seek (bits before : List Bool) :
    evalConfigWithin program (seekState (before.map some) bits) (3 * bits.length + 1) =
      PMF.pure (selectState (bits.reverse ++ before) none []) := by
  induction bits generalizing before with
  | nil => simpa using eval_seek_end before
  | cons bit rest ih =>
      have hBudget : 3 * (bit :: rest).length + 1 = 3 + (3 * rest.length + 1) := by simp; omega
      rw [hBudget, evalConfigWithin_add, eval_seek_bit, PMF.pure_bind]
      simpa [List.map_cons, List.reverse_cons, List.append_assoc] using ih (bit :: before)

private def emptyFinish (current : Option Bool) (after : List (Option Bool)) : Configuration :=
  { pc := 14, inputTape := { right := current :: after }, halted := true }

private def chosenFinish (column : Column) (before : List Bool)
    (current : Option Bool) (after : List (Option Bool)) : Configuration :=
  { pc := if column.multiplier then 18 else 16,
    inputTape := {
      left := (column.modulus :: column.operand :: column.accumulator :: before).map some,
      current := some column.multiplier, right := some false :: current :: after },
    outputTape := { current := some column.multiplier }, halted := true }

private theorem eval_skip (accumulator operand modulus multiplier : Bool)
    (before : List Bool) (current : Option Bool) (after : List (Option Bool)) :
    evalConfigWithin program
      (selectState (false :: multiplier :: modulus :: operand :: accumulator :: before) current after) 7 =
      PMF.pure (selectState before (some accumulator)
        (some operand :: some modulus :: some multiplier :: some false :: current :: after)) := by
  simp [evalConfigWithin, stepPMF, next, program, selectState,
    Instruction.next, Configuration.advance, Configuration.tape,
    Configuration.updateTape, Tape.moveLeft, PMF.pure_bind]

private theorem eval_choose (column : Column)
    (before : List Bool) (current : Option Bool) (after : List (Option Bool)) :
    evalConfigWithin program
      (selectState (true :: column.multiplier :: column.modulus :: column.operand :: column.accumulator :: before)
        current after) 7 = PMF.pure (chosenFinish column before current after) := by
  cases hBit : column.multiplier <;>
    simp [evalConfigWithin, stepPMF, next, program, selectState, chosenFinish, hBit,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.moveLeft, Tape.write, PMF.pure_bind]

private theorem eval_empty (current : Option Bool) (after : List (Option Bool)) :
    evalConfigWithin program (selectState [] current after) 3 = PMF.pure (emptyFinish current after) := by
  simp [evalConfigWithin, stepPMF, next, program, selectState, emptyFinish,
    Instruction.next, Configuration.advance, Configuration.tape,
    Configuration.updateTape, Tape.moveLeft, PMF.pure_bind]

private def finish : List Column → Option Bool → List (Option Bool) → Configuration
  | [], current, after => emptyFinish current after
  | column :: rest, current, after =>
      if column.pending then chosenFinish column ((matrix rest.reverse).reverse) current after
      else finish rest (some column.accumulator)
        (some column.operand :: some column.modulus :: some column.multiplier :: some false :: current :: after)

private theorem finish_halted (columns : List Column) (current : Option Bool) (after : List (Option Bool)) :
    (finish columns current after).halted = true := by
  induction columns generalizing current after with
  | nil => rfl
  | cons column rest ih => simp only [finish]; split <;> simp [chosenFinish, ih]

private theorem eval_halted (c : Configuration) (steps : Nat) (h : c.halted = true) :
    evalConfigWithin program c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]

private theorem reverse_matrix_cons (column : Column) (rest : List Column) :
    (matrix (column :: rest).reverse).reverse = column.pending :: column.multiplier ::
      column.modulus :: column.operand :: column.accumulator :: (matrix rest.reverse).reverse := by
  simp [matrix, row, List.reverse_cons, List.flatMap_append]

private theorem eval_columns (columns : List Column) (current : Option Bool)
    (after : List (Option Bool)) :
    evalConfigWithin program (selectState (matrix columns.reverse).reverse current after)
      (7 * columns.length + 3) = PMF.pure (finish columns current after) := by
  induction columns generalizing current after with
  | nil => simpa [matrix, finish] using eval_empty current after
  | cons column rest ih =>
      have hBudget : 7 * (column :: rest).length + 3 = 7 + (7 * rest.length + 3) := by simp; omega
      rw [hBudget, evalConfigWithin_add, reverse_matrix_cons]
      cases hPending : column.pending with
      | false =>
          simp only [hPending, eval_skip, PMF.pure_bind, ih, finish, Bool.false_eq_true, ↓reduceIte]
      | true =>
          rw [eval_choose column, PMF.pure_bind, eval_halted _ _ rfl]
          simp [finish, hPending]

private theorem finish_output (columns : List Column) (current : Option Bool)
    (after : List (Option Bool)) :
    (finish columns current after).outputBits = (selected columns).toList := by
  induction columns generalizing current after with
  | nil => rfl
  | cons column rest ih =>
      cases hPending : column.pending with
      | false =>
          simpa only [finish, selected, hPending, Bool.false_eq_true, ↓reduceIte] using
            (ih (some column.accumulator)
              (some column.operand :: some column.modulus :: some column.multiplier :: some false :: current :: after))
      | true => simp [finish, selected, hPending, chosenFinish, Configuration.outputBits, Tape.bits]

private theorem finish_input (columns : List Column) (current : Option Bool)
    (after : List (Option Bool)) :
    (finish columns current after).inputTape.bits =
      matrix (consume columns).reverse ++ (current :: after).filterMap id := by
  induction columns generalizing current after with
  | nil => rfl
  | cons column rest ih =>
      cases hPending : column.pending with
      | false =>
          simp [finish, consume, hPending, ih, matrix, row, List.reverse_cons,
            List.flatMap_append, List.append_assoc]
      | true =>
          simp [finish, consume, hPending, chosenFinish, Tape.bits, matrix, row,
            List.reverse_cons, List.flatMap_append, List.filterMap_append, List.append_assoc]


/-- The complete physical return state, including the changed pending flag
and the input head positioned at the selected multiplier bit (or boundary). -/
def selectionFinish (columns : List Column) : Configuration := finish columns.reverse none []

private theorem eval_selection_config (columns : List Column) :
    evalConfigWithin program (Configuration.initial (matrix columns))
      (3 * (matrix columns).length + 1 + (7 * columns.length + 3)) =
      PMF.pure (selectionFinish columns) := by
  have hInitial : Configuration.initial (matrix columns) = seekState [] (matrix columns) := by
    cases matrix columns <;> rfl
  rw [hInitial, evalConfigWithin_add]
  have hSeek := eval_seek (matrix columns) []
  simp only [List.map_nil, List.append_nil] at hSeek
  rw [hSeek, PMF.pure_bind]
  have hColumns := eval_columns columns.reverse none []
  simpa only [List.reverse_reverse, List.length_reverse, selectionFinish] using hColumns

/-- A saved output prefix is already on the caller's physical tape. The
selection code neither reads it nor moves the output head across it. Adding
this prefix to a specification is not an executed tape reset or reload. -/
private def withOutputPrefix (savedOutput : List (Option Bool)) (c : Configuration) : Configuration :=
  { c with outputTape := { c.outputTape with left := c.outputTape.left ++ savedOutput } }

private def prefixResult (savedOutput : List (Option Bool)) :
    Configuration ⊕ (Configuration × Configuration) → Configuration ⊕ (Configuration × Configuration)
  | .inl c => .inl (withOutputPrefix savedOutput c)
  | .inr (c, d) => .inr (withOutputPrefix savedOutput c, withOutputPrefix savedOutput d)

private theorem next_prefix (savedOutput : List (Option Bool)) (c : Configuration) :
    next program (withOutputPrefix savedOutput c) = (next program c).map (prefixResult savedOutput) := by
  cases hActive : c.halted with
  | true => simp [next, withOutputPrefix, hActive]
  | false =>
      by_cases hPc : c.pc < 19
      · interval_cases hIndex : c.pc <;>
          simp [next, program, withOutputPrefix, prefixResult, hActive, hIndex,
            Instruction.next, Configuration.advance, Configuration.tape,
            Configuration.updateTape, Tape.write]
      · have hOutside : program.length ≤ c.pc := by change 19 ≤ c.pc; omega
        simp [next, withOutputPrefix, prefixResult, hActive, List.getElem?_eq_none hOutside]

private theorem stepPMF_prefix (savedOutput : List (Option Bool)) (c : Configuration) :
    stepPMF program (withOutputPrefix savedOutput c) = (stepPMF program c).map (withOutputPrefix savedOutput) := by
  simp only [stepPMF, next_prefix]
  cases hNext : next program c with
  | none => simp [PMF.pure_map]
  | some result =>
      cases result with
      | inl d => simp [prefixResult, PMF.pure_map]
      | inr pair =>
          rcases pair with ⟨d₀, d₁⟩
          simp only [Option.map_some, prefixResult, PMF.map_comp]
          congr 1
          funext bit
          cases bit <;> rfl

private theorem eval_prefix (savedOutput : List (Option Bool)) (c : Configuration) (steps : Nat) :
    evalConfigWithin program (withOutputPrefix savedOutput c) steps =
      (evalConfigWithin program c steps).map (withOutputPrefix savedOutput) := by
  induction steps generalizing c with
  | zero => simp [evalConfigWithin, PMF.pure_map]
  | succ steps ih =>
      rw [evalConfigWithin_succ_head, stepPMF_prefix, PMF.bind_map,
        evalConfigWithin_succ_head, PMF.map_bind]
      simp only [Function.comp_def, ih]

/-- Caller layout for a selection. Only the output head's saved prefix is
parameterized; the contiguous matrix is on the input tape. -/
def selectionStart (columns : List Column) (savedOutput : List (Option Bool)) : Configuration :=
  withOutputPrefix savedOutput (Configuration.initial (matrix columns))

/-- The next iteration starts at the matrix's right boundary, as returned
by the arithmetic phase. The backward selection starts at address 3;
there is no fresh input tape and no uncharged movement to the first bit. -/
def selectionFromEnd (columns : List Column) (savedOutput : List (Option Bool)) : Configuration :=
  { pc := 3, inputTape := { left := (matrix columns).reverse.map some },
    outputTape := { left := savedOutput } }

private theorem finish_outputTape (columns : List Column) (current : Option Bool)
    (after : List (Option Bool)) :
    (finish columns current after).outputTape = { current := selected columns } := by
  induction columns generalizing current after with
  | nil => rfl
  | cons column rest ih =>
      cases hPending : column.pending <;> simp [finish, selected, hPending, chosenFinish, ih]

theorem selectionFinish_outputTape (columns : List Column) :
    (selectionFinish columns).outputTape = { current := selected columns.reverse } :=
  finish_outputTape _ _ _

theorem eval_selection_from_end (columns : List Column) (savedOutput : List (Option Bool)) :
    evalConfigWithin program (selectionFromEnd columns savedOutput)
      (7 * columns.length + 3) =
      PMF.pure { selectionFinish columns with
        outputTape := { (selectionFinish columns).outputTape with left := savedOutput } } := by
  have trace := eval_columns columns.reverse none []
  simp only [List.reverse_reverse, List.length_reverse] at trace
  have startEq : selectionFromEnd columns savedOutput =
      withOutputPrefix savedOutput (selectState (matrix columns).reverse none []) := rfl
  rw [startEq, eval_prefix, trace, PMF.pure_map]
  simp [withOutputPrefix, selectionFinish, finish_outputTape]

theorem selectionFinish_halted (columns : List Column) :
    (selectionFinish columns).halted = true := finish_halted _ _ _

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

private theorem cells_append_blank (bits : List Bool) (index : Nat) :
    (bits.map some ++ [none]).getD index none = (bits.map some).getD index none := by
  induction bits generalizing index with
  | nil => cases index <;> simp
  | cons bit rest ih =>
      cases index with
      | zero => rfl
      | succ index => simpa only [List.map_cons, List.cons_append, List.getD_cons_succ] using ih index

private theorem finish_chosen_split (columns : List Column) (current : Option Bool)
    (after : List (Option Bool)) (tail : List Bool)
    (hTail : current :: after = tail.map some ++ [none])
    (bit : Bool) (hSelected : selected columns = some bit) :
    ∃ (leading remaining : List Bool),
      leading ++ remaining = matrix (consume columns).reverse ++ tail ∧
      (finish columns current after).inputTape.Equivalent
        { Tape.ofBits remaining with left := leading.reverse.map some } := by
  induction columns generalizing current after tail with
  | nil => simp [selected] at hSelected
  | cons column rest ih =>
      cases hPending : column.pending with
      | false =>
          have hRest : selected rest = some bit := by simpa [selected, hPending] using hSelected
          obtain ⟨leading, remaining, hMatrix, hLayout⟩ := ih
            (some column.accumulator)
            (some column.operand :: some column.modulus :: some column.multiplier :: some false :: current :: after)
            ([column.accumulator, column.operand, column.modulus, column.multiplier, false] ++ tail)
            (by simpa only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using
              congrArg (fun cells => some column.accumulator :: some column.operand :: some column.modulus ::
                some column.multiplier :: some false :: cells) hTail) hRest
          refine ⟨leading, remaining, ?_, ?_⟩
          · simpa [consume, hPending, matrix, row, List.reverse_cons,
              List.flatMap_append, List.append_assoc] using hMatrix
          · simpa only [finish, hPending, Bool.false_eq_true, ↓reduceIte] using hLayout
      | true =>
          let leading := matrix rest.reverse ++ [column.accumulator, column.operand, column.modulus]
          let remaining := column.multiplier :: false :: tail
          refine ⟨leading, remaining, ?_, ?_⟩
          · simp [leading, remaining, consume, hPending, matrix, row,
              List.reverse_cons, List.flatMap_append, List.append_assoc]
          · simp only [finish, hPending, ↓reduceIte]
            refine ⟨rfl, ?_, ?_⟩
            · intro index
              simp [chosenFinish, leading, List.reverse_append]
            · intro index
              change (some false :: current :: after).getD index none = (some false :: tail.map some).getD index none
              rw [hTail]
              exact cells_append_blank (false :: tail) index

/-- A successful selection leaves the head inside the updated contiguous
matrix. The split records its real position; rewinding this prefix is a
charged operation of the subsequent arithmetic phase. -/
theorem selectionFinish_chosen_split (columns : List Column) (bit : Bool)
    (hSelected : selected columns.reverse = some bit) :
    ∃ (leading remaining : List Bool),
      leading ++ remaining = matrix (consume columns.reverse).reverse ∧
      (selectionFinish columns).inputTape.Equivalent
        { Tape.ofBits remaining with left := leading.reverse.map some } := by
  simpa only [List.map_nil, List.nil_append, List.append_nil, selectionFinish] using
    finish_chosen_split columns.reverse none [] [] rfl bit hSelected

theorem consume_length (columns : List Column) : (consume columns).length = columns.length := by
  induction columns with
  | nil => rfl
  | cons column rest ih => simp only [consume]; split <;> simp [ih]

private theorem finish_none_input (columns : List Column) (current : Option Bool)
    (after : List (Option Bool)) (hNone : selected columns = none) :
    (finish columns current after).inputTape =
      { right := (matrix columns.reverse).map some ++ current :: after } := by
  induction columns generalizing current after with
  | nil => rfl
  | cons column rest ih =>
      cases hPending : column.pending with
      | true => simp [selected, hPending] at hNone
      | false =>
          have hRest : selected rest = none := by simpa [selected, hPending] using hNone
          simpa [finish, hPending, matrix, row, List.reverse_cons,
            List.flatMap_append, List.map_append, List.append_assoc] using
            ih (some column.accumulator)
              (some column.operand :: some column.modulus :: some column.multiplier :: some false :: current :: after) hRest

theorem selectionFinish_none_input (columns : List Column)
    (hNone : selected columns.reverse = none) :
    (selectionFinish columns).inputTape = { right := (matrix columns).map some ++ [none] } := by
  simpa only [selectionFinish, List.reverse_reverse] using finish_none_input columns.reverse none [] hNone

theorem eval_selection_context (columns : List Column) (savedOutput : List (Option Bool)) :
    evalConfigWithin program (selectionStart columns savedOutput)
      (3 * (matrix columns).length + 1 + (7 * columns.length + 3)) =
      PMF.pure { selectionFinish columns with
        outputTape := { (selectionFinish columns).outputTape with
          left := (selectionFinish columns).outputTape.left ++ savedOutput } } := by
  rw [selectionStart, eval_prefix, eval_selection_config, PMF.pure_map]
  rfl

theorem eval_selection_savedBits (columns : List Column) (savedOutput : List (Option Bool)) :
    (evalConfigWithin program (selectionStart columns savedOutput)
      (3 * (matrix columns).length + 1 + (7 * columns.length + 3))).map
      (fun c => (c.halted, c.inputTape.bits, c.outputBits)) =
      PMF.pure (true, matrix (consume columns.reverse).reverse,
        savedOutput.reverse.filterMap id ++ (selected columns.reverse).toList) := by
  rw [selectionStart, eval_prefix, eval_selection_config, PMF.pure_map, PMF.pure_map]
  have hBits : (withOutputPrefix savedOutput (finish columns.reverse none [])).outputBits =
      savedOutput.reverse.filterMap id ++ (finish columns.reverse none []).outputBits := by
    simp [withOutputPrefix, Configuration.outputBits, Tape.bits,
      List.reverse_append, List.filterMap_append, List.append_assoc]
  change PMF.pure ((finish columns.reverse none []).halted,
    (finish columns.reverse none []).inputTape.bits,
    (withOutputPrefix savedOutput (finish columns.reverse none [])).outputBits) = _
  rw [finish_halted, finish_input, hBits, finish_output]
  simp

/-- The actual halted configuration simultaneously contains the selected
multiplier bit and the matrix with exactly that pending flag consumed. -/
theorem eval_selection (columns : List Column) :
    (evalConfigWithin program (Configuration.initial (matrix columns))
      (3 * (matrix columns).length + 1 + (7 * columns.length + 3))).map
      (fun c => (c.halted, c.inputTape.bits, c.outputBits)) =
      PMF.pure (true, matrix (consume columns.reverse).reverse, (selected columns.reverse).toList) := by
  have hEmpty : selectionStart columns [] = Configuration.initial (matrix columns) := by
    simp [selectionStart, withOutputPrefix, Configuration.initial]
  simpa only [hEmpty, List.reverse_nil, List.filterMap_nil, List.nil_append] using
    eval_selection_savedBits columns []

/-- The native marker update consumes exactly one bit whenever selection
succeeds. This bounds the number of product-loop iterations by the initial
number of flags, without assuming an arithmetic counter instruction. -/
theorem pendingCount_consume (columns : List Column) :
    pendingCount (consume columns) =
      if (selected columns).isSome then pendingCount columns - 1 else pendingCount columns := by
  induction columns with
  | nil => rfl
  | cons column rest ih =>
      cases hPending : column.pending with
      | false => simpa [pendingCount, consume, selected, hPending] using ih
      | true => simp [pendingCount, consume, selected, hPending]

theorem selected_none_iff (columns : List Column) :
    selected columns = none ↔ pendingCount columns = 0 := by
  induction columns with
  | nil => simp [selected, pendingCount]
  | cons column rest ih =>
      cases hPending : column.pending <;> simp [selected, pendingCount, hPending, ih]

theorem pendingCount_consume_eq_sub (columns : List Column) :
    pendingCount (consume columns) = pendingCount columns - 1 := by
  cases hSelected : selected columns with
  | none =>
      have hZero := (selected_none_iff columns).mp hSelected
      simpa [hSelected, hZero] using pendingCount_consume columns
  | some bit => simpa [hSelected] using pendingCount_consume columns

/-- Repeated native selections exhaust the flags in at most the initial
flag count. Arithmetic passes of the complete loop must additionally be
shown to preserve these flags and to return the heads to the next selection. -/
theorem pendingCount_iterate (columns : List Column) (count : Nat) :
    pendingCount (consume^[count] columns) = pendingCount columns - count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply', pendingCount_consume_eq_sub, ih, Nat.sub_sub]

theorem selection_exhausted (columns : List Column) :
    selected (consume^[pendingCount columns] columns) = none := by
  apply (selected_none_iff _).mpr
  rw [pendingCount_iterate, Nat.sub_self]

def initialColumns (columns : List BinaryModularAddition.Column) : List Column :=
  columns.map fun column =>
    { accumulator := false, operand := column.1.1, modulus := column.2,
      multiplier := column.1.2, pending := true }

/-- This is precisely the matrix written by the charged initialization
program; an auxiliary representation does not introduce a free preparation
operation or change the input/output protocol. -/
theorem initialColumns_matrix (columns : List BinaryModularAddition.Column) :
    matrix (initialColumns columns) = BinaryProductInitialization.matrix columns := by
  induction columns with
  | nil => rfl
  | cons column rest ih => simp [matrix, initialColumns, row, BinaryProductInitialization.matrix] at ih ⊢; exact ih

theorem initialColumns_pendingCount (columns : List BinaryModularAddition.Column) :
    pendingCount (initialColumns columns) = columns.length := by
  simp [pendingCount, initialColumns, List.filter_map]

private def rawChosenFinish (bit : Bool) (before : List Bool)
    (current : Option Bool) (after : List (Option Bool)) : Configuration :=
  { pc := if bit then 18 else 16,
    inputTape := {
      left := before.map some, current := some bit,
      right := some false :: current :: after },
    outputTape := { current := some bit }, halted := true }

private theorem eval_raw_choose (bit : Bool) (before : List Bool)
    (current : Option Bool) (after : List (Option Bool)) :
    evalConfigWithin program (selectState (true :: bit :: before) current after) 7 =
      PMF.pure (rawChosenFinish bit before current after) := by
  cases bit <;>
    simp [evalConfigWithin, stepPMF, next, program, selectState, rawChosenFinish,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.moveLeft, Tape.write, PMF.pure_bind]

private def truncatedFinish (current : Option Bool) (after : List (Option Bool)) : Configuration :=
  { pc := 14, inputTape := { right := some false :: current :: after }, halted := true }

private theorem eval_truncated (current : Option Bool) (after : List (Option Bool)) :
    evalConfigWithin program (selectState [true] current after) 6 =
      PMF.pure (truncatedFinish current after) := by
  simp [evalConfigWithin, stepPMF, next, program, selectState, truncatedFinish,
    Instruction.next, Configuration.advance, Configuration.tape,
    Configuration.updateTape, Tape.moveLeft, Tape.write, PMF.pure_bind]

private def skippedShortFinish (rest : List Bool) (current : Option Bool)
    (after : List (Option Bool)) : Configuration :=
  { pc := 14,
    inputTape := (selectState (false :: rest) current after).inputTape.moveLeft.moveLeft.moveLeft.moveLeft.moveLeft.moveLeft,
    halted := true }

private theorem eval_skip_short (rest : List Bool) (hLength : rest.length < 4)
    (current : Option Bool) (after : List (Option Bool)) :
    evalConfigWithin program (selectState (false :: rest) current after) 10 =
      PMF.pure (skippedShortFinish rest current after) := by
  match rest with
  | [] | [_] | [_, _] | [_, _, _] =>
      simp [evalConfigWithin, stepPMF, next, program, selectState, skippedShortFinish,
        Instruction.next, Configuration.advance, Configuration.tape,
        Configuration.updateTape, Tape.moveLeft, PMF.pure_bind]
  | _ :: _ :: _ :: _ :: _ => simp only [List.length_cons] at hLength; omega

private theorem eval_raw (before : List Bool) (current : Option Bool)
    (after : List (Option Bool)) :
    ∃ result : Configuration, result.halted = true ∧
      evalConfigWithin program (selectState before current after) (7 * (before.length + 1)) =
        PMF.pure result := by
  match before with
  | [] =>
      refine ⟨emptyFinish current after, rfl, ?_⟩
      change evalConfigWithin program (selectState [] current after) (3 + 4) = _
      rw [evalConfigWithin_add, eval_empty, PMF.pure_bind]
      exact eval_halted _ _ rfl
  | true :: rest =>
      cases rest with
      | nil =>
          refine ⟨truncatedFinish current after, rfl, ?_⟩
          change evalConfigWithin program (selectState [true] current after) (6 + 8) = _
          rw [evalConfigWithin_add, eval_truncated, PMF.pure_bind]
          exact eval_halted _ _ rfl
      | cons bit rest =>
          refine ⟨rawChosenFinish bit rest current after, rfl, ?_⟩
          have hBudget : 7 * ((true :: bit :: rest).length + 1) = 7 + (7 * (rest.length + 2)) := by simp; omega
          rw [hBudget, evalConfigWithin_add, eval_raw_choose, PMF.pure_bind]
          exact eval_halted _ _ rfl
  | false :: rest =>
      by_cases hLength : rest.length < 4
      · refine ⟨skippedShortFinish rest current after, rfl, ?_⟩
        have hBudget : 7 * ((false :: rest).length + 1) = 10 + (7 * rest.length + 4) := by simp; omega
        rw [hBudget, evalConfigWithin_add, eval_skip_short rest hLength, PMF.pure_bind]
        exact eval_halted _ _ rfl
      · match rest with
        | multiplier :: modulus :: operand :: accumulator :: remaining =>
            obtain ⟨result, hHalted, hEval⟩ := eval_raw remaining (some accumulator)
              (some operand :: some modulus :: some multiplier :: some false :: current :: after)
            refine ⟨result, hHalted, ?_⟩
            have hBudget : 7 * ((false :: multiplier :: modulus :: operand :: accumulator :: remaining).length + 1) =
                7 + (7 * (remaining.length + 1) + 28) := by simp; omega
            rw [hBudget, evalConfigWithin_add, eval_skip, PMF.pure_bind,
              evalConfigWithin_add, hEval, PMF.pure_bind]
            exact eval_halted _ _ hHalted
        | [] | [_] | [_, _] | [_, _, _] => simp at hLength
termination_by before.length

/-- Every raw input, including a malformed partial column, has an explicit
linear stopping bound. Numeric validity is not an assumption of termination. -/
theorem haltsWithin (input : List Bool) : HaltsWithin program input (10 * (input.length + 1)) := by
  obtain ⟨result, hHalted, hEval⟩ := eval_raw input.reverse none []
  have hSeek := eval_seek input []
  simp only [List.map_nil, List.append_nil] at hSeek
  have hInitial : Configuration.initial input = seekState [] input := by cases input <;> rfl
  have hBudget : 10 * (input.length + 1) =
      (3 * input.length + 1) + (7 * (input.length + 1) + 2) := by omega
  intro finish run
  have hSupport := (mem_support_evalConfigWithin_iff program _ finish _).mpr run
  rw [hInitial, hBudget, evalConfigWithin_add, hSeek, PMF.pure_bind, evalConfigWithin_add] at hSupport
  simp only [List.length_reverse] at hEval
  rw [hEval, PMF.pure_bind, eval_halted _ _ hHalted, PMF.mem_support_pure_iff] at hSupport
  exact hSupport ▸ hHalted

theorem polynomialTime : PolynomialTime program :=
  ⟨fun length => 10 * (length + 1),
    (PolynomiallyBounded.const 10).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)), haltsWithin⟩

/-- Saved output cells do not affect termination or its bound. This law
allows selection to follow an arithmetic stage without erasing caller data
or silently replacing the output tape with an empty one. -/
theorem haltsFrom_savedOutput (input : List Bool) (savedOutput : List (Option Bool))
    (result : Configuration)
    (run : PaddedRunsFor program
      { Configuration.initial input with outputTape := { left := savedOutput } }
      result (10 * (input.length + 1))) : result.halted = true := by
  have hStart :
      { Configuration.initial input with outputTape := { left := savedOutput } } =
      withOutputPrefix savedOutput (Configuration.initial input) := by cases input <;> rfl
  have hSupport := (mem_support_evalConfigWithin_iff program _ result _).mpr run
  rw [hStart, eval_prefix, PMF.mem_support_map_iff] at hSupport
  obtain ⟨original, hOriginal, rfl⟩ := hSupport
  exact haltsWithin input original ((mem_support_evalConfigWithin_iff program _ original _).mp hOriginal)

end Machine.BinaryProductSelection
