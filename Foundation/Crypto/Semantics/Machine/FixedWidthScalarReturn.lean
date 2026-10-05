import Foundation.Crypto.Semantics.Machine.AdvanceInputByOutput
import Foundation.Crypto.Semantics.Machine.MoveInputLeftByOutput
import Foundation.Crypto.Semantics.Machine.OutputColumnRewind
import Foundation.Crypto.Semantics.Machine.ContextualInput
import Foundation.Crypto.Semantics.Machine.ContextualFrame
import Foundation.Crypto.Semantics.Machine.NativeSequence
import Foundation.Crypto.Semantics.Machine.OutputFrameCounter

namespace Machine.FixedWidthScalarReturn

def atCells (before rest : List (Option Bool)) : Tape :=
  {({right := rest} : Tape).moveRight with left := before}

private theorem getD_blank (cells : List (Option Bool)) (i : Nat) :
    (cells ++ [none]).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => cases i <;> rfl
  | cons cell rest ih => cases i with
    | zero => rfl
    | succ i => simpa only [List.cons_append, List.getD_cons_succ] using ih i

theorem padded_bits (before : List (Option Bool)) (bits : List Bool) :
    (atCells before (bits.map some ++ [none])).Equivalent {Tape.ofBits bits with left := before} := by
  cases bits with
  | nil => exact Tape.Equivalent.refl _
  | cons bit rest =>
    refine ⟨rfl, fun _ => rfl, ?_⟩
    intro i
    exact getD_blank (rest.map some) i

theorem right_bits (before rest : List (Option Bool)) (bits : List Bool) :
    (Tape.moveRight^[bits.length]) (atCells before (bits.map some ++ rest)) =
      atCells (bits.reverse.map some ++ before) rest := by
  induction bits generalizing before with
  | nil => simp [atCells]
  | cons bit bits ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have moved : (atCells before ((bit::bits).map some ++ rest)).moveRight =
        atCells (some bit::before) (bits.map some ++ rest) := by
      cases h : bits.map some ++ rest <;> simp [atCells, Tape.moveRight, h]
    rw [moved, ih]
    simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem left_bits (before rest : List (Option Bool)) (bits : List Bool) (hRest : rest ≠ []) :
    (Tape.moveLeft^[bits.length]) (atCells (bits.reverse.map some ++ before) rest) =
      atCells before (bits.map some ++ rest) := by
  induction bits using List.reverseRecOn generalizing rest with
  | nil => simp [atCells]
  | append_singleton bits bit ih =>
    rw [List.length_append, List.length_singleton, Function.iterate_succ_apply]
    have moved : (atCells ((bits++[bit]).reverse.map some ++ before) rest).moveLeft =
        atCells (bits.reverse.map some ++ before) (some bit::rest) := by
      cases rest with
      | nil => exact False.elim (hRest rfl)
      | cons cell tail => simp [atCells, Tape.moveLeft, Tape.moveRight, List.reverse_append,
        List.map_append, List.append_assoc]
    rw [moved, ih _ (by simp)]
    simp [List.map_append, List.append_assoc]

/-- Mark the boundary only after the scalar and public power have been
computed. The old first generator cell is no longer needed at return. -/
def markEnd : Program := [.erase .input, .halt]

/-- Physically insert the other scalar boundary; the preceding public
parameter cell is no longer needed after exponentiation. -/
def markStart : Program := [.moveLeft .input, .erase .input, .moveRight .input, .halt]

def program : Program :=
  (((((AdvanceInputByOutput.program.followedBy markEnd).followedBy
    OutputColumnRewind.toFirst).followedBy skipUnary.swapTapes).followedBy
    MoveInputLeftByOutput.program).followedBy markStart).followedBy writeFrame

/-- Start at the same scalar in the retained request. The public-key
payload is used as a real width counter, not a numerical head offset. -/
def start (previous : Option Bool) (saved tail : List (Option Bool))
    (scalar publicKey : List Bool) : Configuration :=
  {inputTape := atCells (previous::saved) (scalar.map some ++ tail), outputTape := {Tape.ofBits publicKey with
      left := (encodeSecurityParameter publicKey.length).reverse.map some}}

def finishInput (saved tail : List (Option Bool)) (scalar : List Bool) : Tape :=
  {left := scalar.reverse.map some ++ none::saved, right := tail.drop 1}

theorem markEnd_runs (before : List (Option Bool)) (current : Option Bool)
    (rest : List (Option Bool)) (output : Tape) :
    RunsFor markEnd
      ({inputTape := {left := before, current := current, right := rest}, outputTape := output} : Configuration)
      ({pc := 1, halted := true, inputTape := {left := before, right := rest}, outputTape := output} : Configuration) 2 := by
  let initial : Configuration := {inputTape := {left := before, current := current, right := rest}, outputTape := output}
  let erased : Configuration := {pc := 1, inputTape := {left := before, right := rest}, outputTape := output}
  have one : Step markEnd initial erased := by
    simp [Step, successors, next, markEnd, initial, erased, Instruction.next,
      Configuration.updateTape, Configuration.advance, Tape.write]
  have two : Step markEnd erased {erased with halted := true} := by
    simp [Step, successors, next, markEnd, erased, Instruction.next]
  exact ((RunsFor.zero _).succ one).succ two

theorem markStart_runs (previous : Option Bool) (saved : List (Option Bool))
    (bit : Bool) (rest : List (Option Bool)) (output : Tape) :
    RunsFor markStart
      ({inputTape := {left := previous::saved, current := some bit, right := rest}, outputTape := output} : Configuration)
      ({pc := 3, halted := true, inputTape := {left := none::saved, current := some bit, right := rest}, outputTape := output} : Configuration) 4 := by
  let initial : Configuration := {inputTape := {left := previous::saved, current := some bit, right := rest}, outputTape := output}
  let moved : Configuration := {pc := 1, inputTape := initial.inputTape.moveLeft, outputTape := output}
  let erased : Configuration := {pc := 2, inputTape := moved.inputTape.write none, outputTape := output}
  let restored : Configuration := {pc := 3, inputTape := erased.inputTape.moveRight, outputTape := output}
  have one : Step markStart initial moved := by simp [Step, successors, next, markStart, initial, moved, Instruction.next, Configuration.updateTape, Configuration.advance]
  have two : Step markStart moved erased := by simp [Step, successors, next, markStart, moved, erased, Instruction.next, Configuration.updateTape, Configuration.advance]
  have three : Step markStart erased restored := by simp [Step, successors, next, markStart, erased, restored, Instruction.next, Configuration.updateTape, Configuration.advance]
  have four : Step markStart restored
      ({pc := 3, halted := true, inputTape := {left := none::saved, current := some bit, right := rest}, outputTape := output} : Configuration) := by
    simp [Step, successors, next, markStart, restored, erased, moved, initial, Tape.moveLeft, Tape.moveRight, Tape.write, Instruction.next]
  exact ((((RunsFor.zero _).succ one).succ two).succ three).succ four

/-- Return the public key and the very scalar which was used to compute
it, by reading retained cells and framing both results on the output tape. -/
theorem runs (previous : Option Bool) (saved : List (Option Bool))
    (nextCell : Option Bool) (tail : List (Option Bool)) (scalar publicKey : List Bool)
    (hWidth : scalar.length = publicKey.length) (hScalar : scalar ≠ []) :
    ∃ target used, used ≤ 50*scalar.length + 80 ∧
      RunsFor program (start previous saved (nextCell::tail) scalar publicKey) target used ∧
      target.halted = true ∧ target.inputTape.Equivalent (finishInput saved (nextCell::tail) scalar) ∧
      target.outputBits = frame publicKey ++ frame scalar := by
  let input := atCells (previous::saved) (scalar.map some ++ nextCell::tail)
  let header := (encodeSecurityParameter publicKey.length).reverse.map some
  let marked : Configuration := {pc := 1, halted := true, inputTape := {left := scalar.reverse.map some ++ previous::saved, right := tail}, outputTape := {left := (frame publicKey).reverse.map some}}
  have forward := AdvanceInputByOutput.runs_any input header publicKey
  have advanced : AdvanceInputByOutput.finishAny input header publicKey =
      ({pc := 4, halted := true, inputTape := {left := scalar.reverse.map some ++ previous::saved, current := nextCell, right := tail}, outputTape := {left := (frame publicKey).reverse.map some}} : Configuration) := by
    simp only [AdvanceInputByOutput.finishAny, ← hWidth, input, right_bits]
    simp [atCells, Tape.moveRight, frame, header, encodeSecurityParameter, List.map_replicate, List.reverse_append, List.map_append, List.append_assoc]
  rw [advanced] at forward
  have stopMark := markEnd_runs (scalar.reverse.map some ++ previous::saved) nextCell tail
    {left := (frame publicKey).reverse.map some}
  obtain ⟨a, u, hu, ra, ha, ai, ao⟩ := forward.followedBy_equivalent stopMark
    (Configuration.Equivalent.refl _) (Nat.zero_le _) rfl rfl rfl
  change marked.inputTape.Equivalent a.inputTape at ai
  change marked.outputTape.Equivalent a.outputTape at ao
  obtain ⟨v, hv, rewind, rewindTape⟩ := OutputColumnRewind.toFirst_runs (frame publicKey) marked.inputTape
  have entryRewind : (rewindBitstringStart (frame publicKey) marked.inputTape).swapTapes.Equivalent (a.resumeAt 0) :=
    ⟨rfl, rfl, ai, ao⟩
  obtain ⟨b, ub, hb, rb, bHalt, bi, bo⟩ := ra.followedBy_equivalent rewind entryRewind
    (Nat.zero_le _) rfl ha rfl
  have bInput : marked.inputTape.Equivalent b.inputTape := bi
  have bOutput : (Tape.ofBits (frame publicKey)).Equivalent b.outputTape := rewindTape.symm.trans bo
  let scan := (skipUnaryCellsStart [] publicKey.length (publicKey.map some ++ [none]) marked.inputTape).swapTapes
  let scanned := (skipUnaryCellsFinish [] publicKey.length (publicKey.map some ++ [none]) marked.inputTape).swapTapes
  have scanning := (skipUnaryCells_runs [] publicKey.length (publicKey.map some ++ [none]) marked.inputTape).swapTapes
  have scanOutput : scan.outputTape.Equivalent (Tape.ofBits (frame publicKey)) := by
    have same : scan.outputTape = atCells [] ((frame publicKey).map some ++ [none]) := by
      simp [scan, skipUnaryCellsStart_layout, Configuration.swapTapes, atCells, frame,
        encodeSecurityParameter, List.map_append, List.map_replicate, List.append_assoc]
    rw [same]
    cases h : frame publicKey <;> simpa [h, Tape.ofBits] using padded_bits [] (frame publicKey)
  have scanEntry : scan.Equivalent (b.resumeAt 0) :=
    ⟨rfl, rfl, bInput, scanOutput.trans bOutput⟩
  obtain ⟨c, uc, hc, rc, cHalt, ci, co⟩ := rb.followedBy_equivalent scanning scanEntry
    (Nat.zero_le _) rfl bHalt rfl
  let backwards := MoveInputLeftByOutput.start marked.inputTape header publicKey
  have counterLayout : backwards.Equivalent (c.resumeAt 0) := by
    refine ⟨rfl, rfl, ci, ?_⟩
    have same : backwards.outputTape.Equivalent scanned.outputTape := by
      have layout : scanned.outputTape = atCells header (publicKey.map some ++ [none]) := by
        cases publicKey with
        | nil =>
          dsimp only [scanned, Configuration.swapTapes]
          simp only [List.length_nil, List.map_nil, List.nil_append]
          rw [skipUnaryCellsFinish_layout]
          simp [atCells, header, encodeSecurityParameter, Tape.moveRight]
        | cons bit rest =>
          dsimp only [scanned, Configuration.swapTapes]
          simp only [List.map_cons, List.cons_append]
          rw [skipUnaryCellsFinish_layout]
          simp [atCells, header, encodeSecurityParameter, Tape.moveRight, List.map_replicate]
      rw [layout]
      exact (padded_bits header publicKey).symm
    exact same.trans co
  have backwardRun := MoveInputLeftByOutput.runs marked.inputTape header publicKey
  have returnedInput : (MoveInputLeftByOutput.finish marked.inputTape header publicKey).inputTape =
      atCells (previous::saved) (scalar.map some ++ none::tail) := by
    change (Tape.moveLeft^[publicKey.length]) (atCells (scalar.reverse.map some ++ previous::saved) (none::tail)) = _
    rw [← hWidth, left_bits _ _ _ (by simp)]
  have returnedOutput : (MoveInputLeftByOutput.finish marked.inputTape header publicKey).outputTape =
      ({left := (frame publicKey).reverse.map some} : Tape) := by
    simp [MoveInputLeftByOutput.finish, frame, header, encodeSecurityParameter, List.map_replicate, List.reverse_append, List.map_append]
  obtain ⟨d, ud, hd, rd, dHalt, di, dout⟩ := rc.followedBy_equivalent backwardRun counterLayout
    (Nat.zero_le _) rfl cHalt rfl
  rw [returnedInput] at di
  rw [returnedOutput] at dout
  cases scalar with
  | nil => exact False.elim (hScalar rfl)
  | cons bit bits =>
    have boundaryRun := markStart_runs previous saved bit (bits.map some ++ none::tail)
      {left := (frame publicKey).reverse.map some}
    have boundaryEntry : ({inputTape := {left := previous::saved, current := some bit, right := bits.map some ++ none::tail}, outputTape := {left := (frame publicKey).reverse.map some}} : Configuration).Equivalent (d.resumeAt 0) :=
      ⟨rfl, rfl, di, dout⟩
    obtain ⟨e, ue, he, re, eHalt, ei, eo⟩ := rd.followedBy_equivalent boundaryRun boundaryEntry
      (Nat.zero_le _) rfl dHalt rfl
    have framing := writeFrameContext_runs saved ((frame publicKey).reverse.map some) tail (bit::bits)
    have frameEntry : (writeFrameContextStart saved ((frame publicKey).reverse.map some) tail (bit::bits)).Equivalent (e.resumeAt 0) := by
      exact ⟨rfl, rfl, ei, eo⟩
    obtain ⟨target, used, bound, run, halt, ti, tout⟩ := re.followedBy_equivalent framing frameEntry
      (Nat.zero_le _) rfl eHalt rfl
    refine ⟨target, used, ?_, run, halt, ti.symm, ?_⟩
    · have frameBound := writeFrameSteps_le (bit::bits)
      have frameLength : (frame publicKey).length = 2*publicKey.length+1 := by simp [frame]; omega
      change u ≤ (4*publicKey.length+2)+2+1 at hu
      change ub ≤ u+v+1 at hb
      change uc ≤ ub+(3*publicKey.length+3)+1 at hc
      change ud ≤ uc+(4*publicKey.length+2)+1 at hd
      change ue ≤ ud+4+1 at he
      omega
    · change target.outputTape.bits = _
      rw [tout.bits.symm]
      simp [writeFrameContextFinish, writeFrameContextPaddedFinish, Configuration.outputBits,
        Tape.bits, List.filterMap_append, List.reverse_append, List.map_append]

/-- Entry variant used after exponentiation has framed the public key. -/
def fromEnd : Program := OutputFrameCounter.program.followedBy program

theorem runs_from_end (previous : Option Bool) (saved : List (Option Bool))
    (nextCell : Option Bool) (tail : List (Option Bool)) (scalar publicKey : List Bool)
    (hWidth : scalar.length = publicKey.length) (hScalar : scalar ≠ []) :
    ∃ target used, used ≤ 57*scalar.length+91 ∧
      RunsFor fromEnd
        ({inputTape := atCells (previous::saved) (scalar.map some ++ nextCell::tail), outputTape := {left := (frame publicKey).reverse.map some}} : Configuration)
        target used ∧ target.halted = true ∧ target.outputBits = frame publicKey ++ frame scalar := by
  obtain ⟨counter, a, ha, countRun, countHalt, ci, co⟩ := OutputFrameCounter.runs
    (atCells (previous::saved) (scalar.map some ++ nextCell::tail)) publicKey
  obtain ⟨returned, b, hb, returnRun, returnHalt, _, bits⟩ := runs previous saved nextCell tail scalar publicKey hWidth hScalar
  have layout : (start previous saved (nextCell::tail) scalar publicKey).Equivalent (counter.resumeAt 0) :=
    ⟨rfl, rfl, ci.symm, co.symm⟩
  obtain ⟨target, used, bound, run, halt, _, out⟩ := countRun.followedBy_equivalent returnRun layout
    (Nat.zero_le _) rfl countHalt returnHalt
  refine ⟨target, used, by omega, run, halt, ?_⟩
  change target.outputTape.bits = _
  exact out.bits.symm.trans bits

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  apply Program.followedBy_no_randomBit
  · apply Program.followedBy_no_randomBit
    · apply Program.followedBy_no_randomBit
      · apply Program.followedBy_no_randomBit
        · apply Program.followedBy_no_randomBit
          · exact Program.followedBy_no_randomBit _ _ AdvanceInputByOutput.no_randomBit (by intro tape; simp [markEnd])
          · exact OutputColumnRewind.toFirst_no_randomBit
        · exact Program.swapTapes_no_randomBit _ skipUnary_no_randomBit
      · exact MoveInputLeftByOutput.no_randomBit
    · intro tape; simp [markStart]
  · exact writeFrame_no_randomBit

theorem fromEnd_no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ fromEnd :=
  Program.followedBy_no_randomBit _ _ OutputFrameCounter.no_randomBit no_randomBit tape

end Machine.FixedWidthScalarReturn
