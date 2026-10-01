import Foundation.Machine.MessageCopy
import Foundation.Machine.MessageSelectionPreparation

namespace Machine

open Foundation.Probability

/-- One fixed native continuation from the end of the normalized response:
rewind, sample the challenge bit, select the message, copy its raw element
code, erase the parser status, and halt. No message bits enter the syntax. -/
def prepareSelectedMessage : Program :=
  let pre := prepareMessageSelection.asSubroutine 0 25
  Program.withSubroutine pre copyMessageField [.halt] 46

private def selectedBefore (beforeInput : List (Option Bool))
    (first : List Bool) (bit : Bool) : List (Option Bool) :=
  if bit then (FiniteBitEncoding.delimit first).reverse.map some ++ some false :: none :: beforeInput
  else some false :: none :: beforeInput

private def selectedTail (second state : List Bool) (blanks : Nat)
    (bit : Bool) : List (Option Bool) :=
  if bit then state.map some ++ none :: List.replicate blanks none
  else (FiniteBitEncoding.delimit second).map some ++ state.map some ++ none :: List.replicate blanks none

def prepareSelectedMessageFinish (beforeInput beforeOutput : List (Option Bool))
    (first second state : List Bool) (blanks : Nat) (bit : Bool) : Configuration :=
  { copyMessageFieldFinish (selectedBefore beforeInput first bit) (none :: some bit :: beforeOutput)
      (if bit then second else first) (selectedTail second state blanks bit) with pc := 46 }

/-- A common worst-case budget for both random branches. The shorter branch
halts before padding; its caller continuation is not treated as a free step. -/
def prepareSelectedMessageSteps (first second state : List Bool) : Nat :=
  prepareMessageSelectionSteps first second state + (8 * (first.length + second.length) + 13)

private theorem selectedPreparation_layout :
    prepareSelectedMessage = Program.withSubroutine [] prepareMessageSelection
      (copyMessageField.asSubroutine 25 46 ++ [.halt]) 25 := rfl

private theorem selectedCopy_start (beforeInput beforeOutput : List (Option Bool))
    (first second state : List Bool) (blanks : Nat) (bit : Bool) :
    (prepareMessageSelectionFinish beforeInput beforeOutput first second state blanks bit).resumeAt 0 =
      readDelimitedContextStart (selectedBefore beforeInput first bit)
        (none :: some bit :: beforeOutput) (if bit then second else first)
        (selectedTail second state blanks bit) := by
  simpa [prepareMessageSelectionFinish, Configuration.resumeAt, selectedBefore, selectedTail,
    List.append_assoc] using selectMessageFinish_copy_layout (none :: beforeInput) beforeOutput
      first second (state.map some ++ none :: List.replicate blanks none) bit

private theorem selectedCopy_eval_exact (beforeInput beforeOutput : List (Option Bool))
    (first second state : List Bool) (blanks : Nat) (bit : Bool) :
    evalConfigWithin prepareSelectedMessage
      ((prepareMessageSelectionFinish beforeInput beforeOutput first second state blanks bit).resumeAt 25)
      (readDelimitedSteps (FiniteBitEncoding.delimit (if bit then second else first)) + 4) =
      PMF.pure (prepareSelectedMessageFinish beforeInput beforeOutput first second state blanks bit) := by
  let pre := prepareMessageSelection.asSubroutine 0 25
  have hCopy := (copyMessageField_runs (selectedBefore beforeInput first bit)
      (none :: some bit :: beforeOutput) (if bit then second else first)
      (selectedTail second state blanks bit)).evalConfigWithin_withSubroutine_halted_of_closed
    pre copyMessageField [.halt] 46 (by change 0 < 20; decide) rfl rfl
    copyMessageField_control_closed copyMessageField_no_randomBit
  rw [← selectedCopy_start] at hCopy
  change evalConfigWithin prepareSelectedMessage
    ((prepareMessageSelectionFinish beforeInput beforeOutput first second state blanks bit).resumeAt 25)
    (readDelimitedSteps (FiniteBitEncoding.delimit (if bit then second else first)) + 3) =
      PMF.pure ((prepareSelectedMessageFinish beforeInput beforeOutput first second state blanks bit).resumeAt 46) at hCopy
  have hInstruction : prepareSelectedMessage[46]? = some .halt := by
    have h := Program.withSubroutine_getElem?_suffix pre copyMessageField [.halt] 46 0
    change prepareSelectedMessage[46]? = some .halt at h
    exact h
  rw [show readDelimitedSteps (FiniteBitEncoding.delimit (if bit then second else first)) + 4 =
    (readDelimitedSteps (FiniteBitEncoding.delimit (if bit then second else first)) + 3) + 1 by omega,
    evalConfigWithin_add, hCopy, PMF.pure_bind]
  simp [evalConfigWithin, stepPMF, next, Configuration.resumeAt, hInstruction,
    Instruction.next, PMF.pure_bind, prepareSelectedMessageFinish, copyMessageFieldFinish,
    readDelimitedContextFinish]

private theorem selectedCopy_eval_padded (beforeInput beforeOutput : List (Option Bool))
    (first second state : List Bool) (blanks : Nat) (bit : Bool) (extra : Nat) :
    evalConfigWithin prepareSelectedMessage
      ((prepareMessageSelectionFinish beforeInput beforeOutput first second state blanks bit).resumeAt 25)
      ((8 * (first.length + second.length) + 13) + extra) =
      PMF.pure (prepareSelectedMessageFinish beforeInput beforeOutput first second state blanks bit) := by
  let cost := readDelimitedSteps (FiniteBitEncoding.delimit (if bit then second else first)) + 4
  have hCost : cost ≤ 8 * (first.length + second.length) + 13 := by
    have h := copyMessageField_steps_le (if bit then second else first)
    cases bit <;> dsimp [cost] <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> omega
  rw [show (8 * (first.length + second.length) + 13) + extra =
      cost + ((8 * (first.length + second.length) + 13) + extra - cost) by omega,
    evalConfigWithin_add, selectedCopy_eval_exact, PMF.pure_bind]
  have hHalted : (prepareSelectedMessageFinish beforeInput beforeOutput first second state blanks bit).halted = true := rfl
  generalize ((8 * (first.length + second.length) + 13) + extra - cost) = remaining
  induction remaining with
  | zero => rfl
  | succ remaining ih => simp [evalConfigWithin, ih, stepPMF, next, hHalted]

/-- Complete configuration distribution for the actual native selection and
copy continuation. The same sampled bit both selects the copied message and
remains stored behind its blank separator. Both random branches halt. -/
theorem prepareSelectedMessage_eval (beforeInput beforeOutput : List (Option Bool))
    (first second state : List Bool) (blanks : Nat) :
    evalConfigWithin prepareSelectedMessage
      (prepareMessageSelectionStart beforeInput beforeOutput first second state blanks)
      (prepareSelectedMessageSteps first second state) =
      sampleBit.map (prepareSelectedMessageFinish beforeInput beforeOutput first second state blanks) := by
  let start := prepareMessageSelectionStart beforeInput beforeOutput first second state blanks
  let steps := prepareMessageSelectionSteps first second state
  let tail := 8 * (first.length + second.length) + 13
  have hReturn := Program.evalReturnWithin_configuration_eq_of_halted
    [] prepareMessageSelection (copyMessageField.asSubroutine 25 46 ++ [.halt]) 25
    (by intro pc h; change pc ≤ 24 at h; simp only [List.length_nil, Nat.zero_add]; omega)
    start (by change 0 ≤ 24; decide) rfl steps
    (prepareMessageSelection_haltsFrom beforeInput beforeOutput first second state blanks)
  rw [← selectedPreparation_layout] at hReturn
  change evalReturnWithin prepareSelectedMessage 25 start steps = _ at hReturn
  rw [prepareMessageSelection_eval, PMF.map_comp] at hReturn
  have hTail (bit : Bool) : evalConfigWithin prepareSelectedMessage
      ((prepareMessageSelectionFinish beforeInput beforeOutput first second state blanks bit).resumeAt 25)
      tail = PMF.pure (prepareSelectedMessageFinish beforeInput beforeOutput first second state blanks bit) := by
    simpa only [Nat.add_zero] using selectedCopy_eval_padded beforeInput beforeOutput first second state blanks bit 0
  have hAfter := evalConfigWithin_after_return prepareSelectedMessage 25 start steps tail id (by
    intro d hd _hPc extra
    rw [hReturn, PMF.mem_support_map_iff] at hd
    obtain ⟨bit, _hBit, rfl⟩ := hd
    simp only [Function.comp_def, PMF.map_id]
    change evalConfigWithin prepareSelectedMessage
      ((prepareMessageSelectionFinish beforeInput beforeOutput first second state blanks bit).resumeAt 25)
      ((8 * (first.length + second.length) + 13) + extra) = _
    rw [selectedCopy_eval_padded, hTail])
  simp only [PMF.map_id] at hAfter
  change evalConfigWithin prepareSelectedMessage start (steps + tail) = _
  rw [hAfter, hReturn, PMF.bind_map]
  simp only [Function.comp_def]
  simp_rw [hTail]
  exact PMF.bind_pure_comp _ _

theorem prepareSelectedMessage_haltsFrom (beforeInput beforeOutput : List (Option Bool))
    (first second state : List Bool) (blanks : Nat) (finish : Configuration)
    (run : PaddedRunsFor prepareSelectedMessage
      (prepareMessageSelectionStart beforeInput beforeOutput first second state blanks)
      finish (prepareSelectedMessageSteps first second state)) : finish.halted = true := by
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [prepareSelectedMessage_eval, PMF.mem_support_map_iff] at hMem
  obtain ⟨bit, _hBit, rfl⟩ := hMem
  rfl

theorem prepareSelectedMessage_steps_le (first second state : List Bool) :
    prepareSelectedMessageSteps first second state ≤
      14 * (canonicalMessageBits first second state).length + 27 := by
  have h := prepareMessageSelection_steps_le first second state
  have hSize : first.length + second.length ≤ (canonicalMessageBits first second state).length := by
    simp [canonicalMessageBits, FiniteBitEncoding.delimit_length]
    omega
  simp only [prepareSelectedMessageSteps]
  omega

theorem prepareSelectedMessageFinish_output (beforeInput beforeOutput : List (Option Bool))
    (first second state : List Bool) (blanks : Nat) (bit : Bool) :
    (prepareSelectedMessageFinish beforeInput beforeOutput first second state blanks bit).outputTape =
      { left := (if bit then second else first).reverse.map some ++ none :: some bit :: beforeOutput,
        right := [none] } := rfl

/-- The prefix actually consumed on the canonical response tape. A false
challenge consumes the first field only; a true challenge consumes both. -/
def selectedMessageConsumed (first second : List Bool) (bit : Bool) : List Bool :=
  false :: (FiniteBitEncoding.delimit first ++ if bit then FiniteBitEncoding.delimit second else [])

def selectedMessageRemaining (second state : List Bool) (bit : Bool) : List Bool :=
  if bit then state else FiniteBitEncoding.delimit second ++ state

theorem selectedMessage_partition (first second state : List Bool) (bit : Bool) :
    selectedMessageConsumed first second bit ++ selectedMessageRemaining second state bit =
      canonicalMessageBits first second state := by
  cases bit <;> simp [selectedMessageConsumed, selectedMessageRemaining, canonicalMessageBits, List.append_assoc]

theorem selectedMessageConsumed_length_le (first second state : List Bool) (bit : Bool) :
    (selectedMessageConsumed first second bit).length ≤ (canonicalMessageBits first second state).length := by
  rw [← selectedMessage_partition first second state bit]
  simp

/-- The original canonical response remains on the input tape, split at
the end of the selected field. All saved blocks before its blank separator
and all represented trailing blank cells are preserved. -/
theorem prepareSelectedMessageFinish_input (beforeInput beforeOutput : List (Option Bool))
    (first second state : List Bool) (blanks : Nat) (bit : Bool) :
    (prepareSelectedMessageFinish beforeInput beforeOutput first second state blanks bit).inputTape =
      { ({ right := (selectedMessageRemaining second state bit).map some ++
          none :: List.replicate blanks none } : Tape).moveRight with
        left := (selectedMessageConsumed first second bit).reverse.map some ++ none :: beforeInput } := by
  simp only [prepareSelectedMessageFinish, copyMessageFieldFinish]
  rw [readDelimitedContextFinish_input]
  cases bit <;> simp [selectedBefore, selectedTail, selectedMessageConsumed,
    selectedMessageRemaining, List.reverse_cons, List.reverse_append, List.map_append, List.append_assoc]

/-- The complete native rewind/select/copy stage halts on every finite
pair of caller tapes, including malformed normalization output. The source
random bit, parser work, status erasure and caller halt are all charged. -/
theorem prepareSelectedMessage_haltsFrom_anyTape (input output : Tape) (finish : Configuration)
    (run : PaddedRunsFor prepareSelectedMessage
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (400 * (input.cells + output.cells) + 500)) : finish.halted = true := by
  let initial : Configuration := { inputTape := input, outputTape := output }
  let storage := input.cells + output.cells
  let firstTime := 40 * storage + 50
  let secondTime := 8 * (storage + firstTime) + 9
  have hFirst (c : Configuration) (trace : PaddedRunsFor prepareMessageSelection initial c firstTime) :
      c.halted = true := prepareMessageSelection_haltsFrom_anyTape input output c trace
  have hSecond (c : Configuration) (hc : c ∈ (evalConfigWithin prepareMessageSelection initial firstTime).support)
      (d : Configuration) (trace : PaddedRunsFor copyMessageField (c.resumeAt 0) d secondTime) :
      d.halted = true := by
    have hStorage := GuardedCompiler.sourceStorage_le_of_padded_run
      ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
    change c.inputTape.cells + c.outputTape.cells ≤ storage + firstTime at hStorage
    have hBound : 8 * c.inputTape.cells + 9 ≤ secondTime := by dsimp only [secondTime]; omega
    have hAt (target : Configuration)
        (targetTrace : PaddedRunsFor copyMessageField (c.resumeAt 0) target (8 * c.inputTape.cells + 9)) :
        target.halted = true := copyMessageField_haltsFrom_anyTape c.inputTape c.outputTape target targetTrace
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
    rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hAt] at hMem
    exact hAt d ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem)
  have hLaw := Program.evalConfigWithin_twoStages prepareMessageSelection copyMessageField initial
    rfl rfl firstTime secondTime hFirst hSecond
  change (evalConfigWithin prepareSelectedMessage initial (firstTime + (secondTime + 1))).map
    (fun c => (c.halted, c.outputBits)) = _ at hLaw
  have hAt (target : Configuration)
      (trace : PaddedRunsFor prepareSelectedMessage initial target (firstTime + (secondTime + 1))) :
      target.halted = true := by
    have hMem : (target.halted, target.outputBits) ∈
        ((evalConfigWithin prepareSelectedMessage initial (firstTime + (secondTime + 1))).map
          (fun c => (c.halted, c.outputBits))).support := by
      rw [PMF.mem_support_map_iff]
      exact ⟨target, (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace, rfl⟩
    rw [hLaw, PMF.mem_support_bind_iff] at hMem
    obtain ⟨c, hc, hOutput⟩ := hMem
    rw [PMF.mem_support_map_iff] at hOutput
    obtain ⟨d, hd, hSame⟩ := hOutput
    exact (congrArg Prod.fst hSame).symm.trans
      (hSecond c hc d ((mem_support_evalConfigWithin_iff _ _ _ _).mp hd))
  have hBound : firstTime + (secondTime + 1) ≤ 400 * (input.cells + output.cells) + 500 := by
    dsimp only [firstTime, secondTime, storage]
    omega
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hAt] at hMem
  exact hAt finish ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem)

/-- Every branch leaves an actual fresh output frontier after selection
and status erasure, even if the retained response is malformed. The full
configuration composition law keeps both physical tapes available; no
canonical-response decoder or tape replacement is used in this proof. -/
theorem prepareSelectedMessage_output_layout_anyTape (input : Tape)
    (savedOutput : List (Option Bool)) (blanks : Nat) (finish : Configuration)
    (run : PaddedRunsFor prepareSelectedMessage
      ({ inputTape := input, outputTape := { left := savedOutput, right := List.replicate blanks none } } : Configuration)
      finish (400 * (input.cells +
        ({ left := savedOutput, right := List.replicate blanks none } : Tape).cells) + 500)) :
    ∃ after remaining, finish.outputTape = { left := after, right := List.replicate remaining none } := by
  let output : Tape := { left := savedOutput, right := List.replicate blanks none }
  let initial : Configuration := { inputTape := input, outputTape := output }
  let storage := input.cells + output.cells
  let firstTime := 40 * storage + 50
  let secondTime := 8 * (storage + firstTime) + 9
  obtain ⟨selected, hSelected, hSelectedFinish⟩ := prepareMessageSelection_eval_anyTape input output
  change evalConfigWithin prepareMessageSelection initial firstTime =
    Foundation.Probability.sampleBit.map selected at hSelected
  have hFirst (c : Configuration) (trace : PaddedRunsFor prepareMessageSelection initial c firstTime) :
      c.halted = true := prepareMessageSelection_haltsFrom_anyTape input output c trace
  have hSecond (c : Configuration) (hc : c ∈ (evalConfigWithin prepareMessageSelection initial firstTime).support)
      (d : Configuration) (trace : PaddedRunsFor copyMessageField (c.resumeAt 0) d secondTime) :
      d.halted = true ∧
        ∃ after remaining, d.outputTape = { left := after, right := List.replicate remaining none } := by
    have hStorage := GuardedCompiler.sourceStorage_le_of_padded_run
      ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
    change c.inputTape.cells + c.outputTape.cells ≤ storage + firstTime at hStorage
    have hBound : 8 * c.inputTape.cells + 9 ≤ secondTime := by dsimp only [secondTime]; omega
    have hAt (target : Configuration)
        (targetTrace : PaddedRunsFor copyMessageField (c.resumeAt 0) target (8 * c.inputTape.cells + 9)) :
        target.halted = true := copyMessageField_haltsFrom_anyTape c.inputTape c.outputTape target targetTrace
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
    rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hAt] at hMem
    have localRun := (mem_support_evalConfigWithin_iff _ _ _ _).mp hMem
    rw [hSelected, PMF.mem_support_map_iff] at hc
    obtain ⟨bit, _hBit, rfl⟩ := hc
    have hOutput : (selected bit).outputTape =
        { left := none :: some bit :: savedOutput, right := List.replicate (blanks - 2) none } := by
      rw [(hSelectedFinish bit).2]
      cases blanks with
      | zero => rfl
      | succ count => cases count <;> simp [output, Tape.write, Tape.moveRight, List.replicate_succ]
    change PaddedRunsFor copyMessageField
      ({ inputTape := (selected bit).inputTape, outputTape := (selected bit).outputTape } : Configuration)
      d (8 * (selected bit).inputTape.cells + 9) at localRun
    rw [hOutput] at localRun
    exact copyMessageField_haltsFrom_with_output_layout _ _ _ d localRun
  have hLaw := Program.evalConfigWithin_twoStages_configuration prepareMessageSelection copyMessageField initial
    rfl rfl firstTime secondTime hFirst (by intro c hc d trace; exact (hSecond c hc d trace).1)
  change evalConfigWithin prepareSelectedMessage initial (firstTime + (secondTime + 1)) =
    (evalConfigWithin prepareMessageSelection initial firstTime).bind
      (fun c => (evalConfigWithin copyMessageField (c.resumeAt 0) secondTime).map
        (fun d => { d with pc := 46, halted := true })) at hLaw
  have hAt (target : Configuration)
      (trace : PaddedRunsFor prepareSelectedMessage initial target (firstTime + (secondTime + 1))) :
      target.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
    rw [hLaw, PMF.mem_support_bind_iff] at hMem
    obtain ⟨c, _hc, hd⟩ := hMem
    rw [PMF.mem_support_map_iff] at hd
    obtain ⟨d, _hd, rfl⟩ := hd
    rfl
  have hBound : firstTime + (secondTime + 1) ≤ 400 * storage + 500 := by
    dsimp only [firstTime, secondTime]
    omega
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hAt, hLaw, PMF.mem_support_bind_iff] at hMem
  obtain ⟨c, hc, hd⟩ := hMem
  rw [PMF.mem_support_map_iff] at hd
  obtain ⟨d, hd, rfl⟩ := hd
  exact (hSecond c hc d ((mem_support_evalConfigWithin_iff _ _ _ _).mp hd)).2

/-- Standalone selection/copy is polynomial time on all raw bitstrings,
not merely on the canonical responses used by its correctness theorem. -/
theorem prepareSelectedMessage_polynomialTime : PolynomialTime prepareSelectedMessage := by
  refine ⟨fun m => 400 * (m + 2) + 500, ?_, ?_⟩
  · exact ((PolynomiallyBounded.const 400).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2))).add
      (PolynomiallyBounded.const 500)
  · intro input
    have hAt : HaltsWithin prepareSelectedMessage input
        (400 * ((Configuration.initial input).inputTape.cells + (Configuration.initial input).outputTape.cells) + 500) :=
      fun finish run => prepareSelectedMessage_haltsFrom_anyTape _ _ finish run
    apply hAt.mono
    cases input <;> simp [Configuration.initial, Tape.ofBits, Tape.cells]
    omega


/-- A finite contiguous raw response stays contiguous ahead of the input
head after native rewind, randomized selection and field copying. This
includes empty responses and malformed escaped fields. Saved caller cells
behind the head are neither reloaded nor required to be canonical. -/
theorem prepareSelectedMessage_input_raw_frontier (input output : Tape)
    (raw : List Bool) (blanks : Nat)
    (hForward : input.current :: input.right = raw.map some ++ none :: List.replicate blanks none)
    (finish : Configuration)
    (run : PaddedRunsFor prepareSelectedMessage
      ({ inputTape := input, outputTape := output } : Configuration) finish
      (400 * (input.cells + output.cells) + 500)) :
    ∃ (remaining : List Bool) (padding : Nat),
      finish.inputTape.current :: finish.inputTape.right =
        remaining.map some ++ none :: List.replicate padding none := by
  let initial : Configuration := { inputTape := input, outputTape := output }
  let storage := input.cells + output.cells
  let firstTime := 40 * storage + 50
  let secondTime := 8 * (storage + firstTime) + 9
  obtain ⟨selected, hSelected, hSelectedFinish⟩ :=
    prepareMessageSelection_eval_with_input_layout input output
  change evalConfigWithin prepareMessageSelection initial firstTime =
    Foundation.Probability.sampleBit.map selected at hSelected
  have hFirst (c : Configuration) (trace : PaddedRunsFor prepareMessageSelection initial c firstTime) :
      c.halted = true := prepareMessageSelection_haltsFrom_anyTape input output c trace
  have hSecond (c : Configuration)
      (hc : c ∈ (evalConfigWithin prepareMessageSelection initial firstTime).support)
      (d : Configuration) (trace : PaddedRunsFor copyMessageField (c.resumeAt 0) d secondTime) :
      d.halted = true := by
    have hStorage := GuardedCompiler.sourceStorage_le_of_padded_run
      ((mem_support_evalConfigWithin_iff _ _ _ _).mp hc)
    change c.inputTape.cells + c.outputTape.cells ≤ storage + firstTime at hStorage
    have hBound : 8 * c.inputTape.cells + 9 ≤ secondTime := by dsimp only [secondTime]; omega
    have hAt (target : Configuration)
        (targetTrace : PaddedRunsFor copyMessageField (c.resumeAt 0) target (8 * c.inputTape.cells + 9)) :
        target.halted = true := copyMessageField_haltsFrom_anyTape c.inputTape c.outputTape target targetTrace
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
    rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hAt] at hMem
    exact hAt d ((mem_support_evalConfigWithin_iff _ _ _ _).mp hMem)
  have hLaw := Program.evalConfigWithin_twoStages_configuration prepareMessageSelection copyMessageField initial
    rfl rfl firstTime secondTime hFirst hSecond
  change evalConfigWithin prepareSelectedMessage initial (firstTime + (secondTime + 1)) = _ at hLaw
  have hSmall (target : Configuration)
      (trace : PaddedRunsFor prepareSelectedMessage initial target (firstTime + (secondTime + 1))) :
      target.halted = true := by
    have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
    rw [hLaw, PMF.mem_support_bind_iff] at hMem
    obtain ⟨middle, _hMiddle, hTarget⟩ := hMem
    rw [PMF.mem_support_map_iff] at hTarget
    obtain ⟨last, _hLast, rfl⟩ := hTarget
    rfl
  have hBound : firstTime + (secondTime + 1) ≤ 400 * (input.cells + output.cells) + 500 := by
    dsimp only [firstTime, secondTime, storage]
    omega
  have hMem := (mem_support_evalConfigWithin_iff _ _ _ _).mpr run
  rw [evalConfigWithin_eq_of_le _ _ _ _ hBound hSmall, hLaw, PMF.mem_support_bind_iff] at hMem
  obtain ⟨middle, hMiddle, hTarget⟩ := hMem
  rw [PMF.mem_support_map_iff] at hTarget
  obtain ⟨last, hLast, rfl⟩ := hTarget
  rw [hSelected, PMF.mem_support_map_iff] at hMiddle
  obtain ⟨bit, _hBit, rfl⟩ := hMiddle
  obtain ⟨rest, padding, hRest⟩ := (hSelectedFinish bit).2.2 raw blanks hForward
  obtain ⟨moves, _hMoves, hMoved⟩ :=
    copyMessageField_input_moveRight ((mem_support_evalConfigWithin_iff _ _ _ _).mp hLast)
  change ∃ (remaining : List Bool) (padding : Nat),
    last.inputTape.current :: last.inputTape.right = remaining.map some ++ none :: List.replicate padding none
  rw [hMoved]
  exact moveRight_iterate_raw_frontier (selected bit).inputTape rest padding moves hRest

end Machine
