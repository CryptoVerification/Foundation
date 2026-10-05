import Foundation.Crypto.Semantics.Machine.DelimitedInput

namespace Machine.ChooseFirstField

/-- A native first stage of choose-response validation. The leading bit must
be the choose tag `false`; the following self-delimiting field is parsed by
`readDelimited`. The payload and a success bit remain on the output tape.
The rejected-tag branch also writes a failure bit. No decoder is an opcode. -/
private def tagPrefix : Program :=
  [.branch .input 20 1 20, .moveRight .input]

def program : Program :=
  Program.withSubroutine tagPrefix readDelimited
    [.halt, .write .output false, .halt] 19

theorem length : program.length = 22 := by
  decide

theorem no_randomBit (tape : TapeId) :
    Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

private theorem lookup_tag :
    program[0]? = some (.branch .input 20 1 20) := by native_decide

private theorem lookup_advance :
    program[1]? = some (.moveRight .input) := by native_decide

private theorem lookup_accept : program[19]? = some .halt := by native_decide
private theorem lookup_reject_write :
    program[20]? = some (.write .output false) := by native_decide
private theorem lookup_reject_halt : program[21]? = some .halt := by native_decide

private theorem prefix_run (rest : List Bool) :
    RunsFor program (Configuration.initial (false :: rest))
      ((readDelimitedStart [some false] [] rest).rebasePc 2) 2 := by
  let start := Configuration.initial (false :: rest)
  let selected : Configuration := { start with pc := 1 }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, lookup_tag, start, selected,
      Configuration.initial, Instruction.next, Configuration.tape, Tape.ofBits]
  have hMove : Step program selected
      ((readDelimitedStart [some false] [] rest).rebasePc 2) := by
    cases rest <;>
      simp [Step, successors, next, lookup_advance, start, selected,
        Configuration.initial, readDelimitedStart, Instruction.next,
        Configuration.updateTape, Configuration.advance, Configuration.rebasePc,
        Tape.moveRight, Tape.ofBits]
    all_goals exact ⟨rfl, rfl, rfl, rfl⟩
  exact ((RunsFor.zero _).succ hBranch).succ hMove

private theorem returned_halt (c : Configuration) :
    RunsFor program (c.resumeAt 19)
      { c.resumeAt 19 with halted := true } 1 := by
  apply (RunsFor.zero _).succ
  simp [Step, successors, next, lookup_accept, Configuration.resumeAt,
    Instruction.next]

/-- The actual finite code consumes the choose tag and one terminated field.
This statement includes a malformed inner field; its status bit then is false. -/
theorem runs_tag_false (rest : List Bool) :
    ∃ used ≤ 2 + readDelimitedSteps rest + 1,
      RunsFor program (Configuration.initial (false :: rest))
        { (readDelimitedFinish [some false] [] rest).resumeAt 19 with halted := true }
        used := by
  obtain ⟨used, hUsed, hParser⟩ :=
    (readDelimited_runs [some false] [] rest).withSubroutine_halted
      tagPrefix readDelimited [.halt, .write .output false, .halt] 19
      (by change 0 ≤ 16; omega) rfl rfl
  change RunsFor program
    ((readDelimitedStart [some false] [] rest).rebasePc 2)
    ((readDelimitedFinish [some false] [] rest).resumeAt 19)
    used at hParser
  refine ⟨2 + used + 1, by omega, ?_⟩
  exact ((prefix_run rest).trans hParser).trans
    (returned_halt (readDelimitedFinish [some false] [] rest))

/-- The same parser can be invoked after earlier request fields have been
consumed. Those cells stay to the left of the input head. -/
theorem runs_tag_false_from (before : List (Option Bool)) (rest : List Bool) :
    ∃ used ≤ 2 + readDelimitedSteps rest + 1,
      RunsFor program
        ({ inputTape := { Tape.ofBits (false :: rest) with left := before } } : Configuration)
        { (readDelimitedFinish (some false :: before) [] rest).resumeAt 19 with
          halted := true } used := by
  let start : Configuration :=
    { inputTape := { Tape.ofBits (false :: rest) with left := before } }
  let selected : Configuration := { start with pc := 1 }
  have hBranch : Step program start selected := by
    simp [Step, successors, next, lookup_tag, start, selected,
      Instruction.next, Configuration.tape, Tape.ofBits]
  have hMove : Step program selected
      ((readDelimitedStart (some false :: before) [] rest).rebasePc 2) := by
    cases rest <;>
      simp [Step, successors, next, lookup_advance, start, selected,
        readDelimitedStart, Instruction.next,
        Configuration.updateTape, Configuration.advance, Configuration.rebasePc,
        Tape.moveRight, Tape.ofBits]
    all_goals exact ⟨rfl, rfl, rfl, rfl⟩
  have hPrefix : RunsFor program start
      ((readDelimitedStart (some false :: before) [] rest).rebasePc 2) 2 :=
    ((RunsFor.zero _).succ hBranch).succ hMove
  obtain ⟨used, hUsed, hParser⟩ :=
    (readDelimited_runs (some false :: before) [] rest).withSubroutine_halted
      tagPrefix readDelimited [.halt, .write .output false, .halt] 19
      (by change 0 ≤ 16; omega) rfl rfl
  change RunsFor program
    ((readDelimitedStart (some false :: before) [] rest).rebasePc 2)
    ((readDelimitedFinish (some false :: before) [] rest).resumeAt 19)
    used at hParser
  refine ⟨2 + used + 1, by omega, ?_⟩
  exact (hPrefix.trans hParser).trans
    (returned_halt (readDelimitedFinish (some false :: before) [] rest))

private def rejectedFinish (bits : List Bool) : Configuration :=
  { pc := 21, inputTape := Tape.ofBits bits,
    outputTape := Tape.ofBits [false], halted := true }

/-- Wrong-stage and empty replies take a fixed three-step rejecting path. -/
theorem runs_bad_tag (bits : List Bool)
    (h : bits.head? ≠ some false) :
    RunsFor program (Configuration.initial bits) (rejectedFinish bits) 3 := by
  let start := Configuration.initial bits
  let selected : Configuration := { start with pc := 20 }
  let written : Configuration :=
    { selected with pc := 21, outputTape := selected.outputTape.write (some false) }
  have hBranch : Step program start selected := by
    cases bits with
    | nil =>
        simp [Step, successors, next, lookup_tag, start, selected,
          Configuration.initial, Instruction.next, Configuration.tape, Tape.ofBits]
    | cons bit rest =>
        cases bit with
        | false => simp at h
        | true =>
            simp [Step, successors, next, lookup_tag, start, selected,
              Configuration.initial, Instruction.next, Configuration.tape, Tape.ofBits]
  have hWrite : Step program selected written := by
    simp [Step, successors, next, lookup_reject_write, start, selected, written,
      Configuration.initial, Instruction.next, Configuration.updateTape,
      Configuration.advance]
  have hHalt : Step program written (rejectedFinish bits) := by
    simp [Step, successors, next, lookup_reject_halt,
      start, selected, written,
      rejectedFinish, Configuration.initial, Instruction.next, Tape.write, Tape.ofBits]
  exact (((RunsFor.zero _).succ hBranch).succ hWrite).succ hHalt

/-- A uniform bound on all finite replies, including a truncated delimiter. -/
def budget (length : Nat) : Nat := 4 * (length + 1) + 8

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits (budget bits.length) := by
  cases bits with
  | nil =>
      have hRun := runs_bad_tag [] (by simp)
      have hHalt : HaltsWith program [] (rejectedFinish []).outputBits 3 :=
        ⟨_, hRun, rfl, rfl⟩
      exact (hHalt.haltsWithin_of_no_randomBit no_randomBit).mono
        (by simp [budget])
  | cons tag rest =>
      cases tag with
      | false =>
          obtain ⟨used, hUsed, hRun⟩ := runs_tag_false rest
          let finish : Configuration :=
            { (readDelimitedFinish [some false] [] rest).resumeAt 19 with halted := true }
          have hHalt : HaltsWith program (false :: rest) finish.outputBits used :=
            ⟨_, hRun, rfl, rfl⟩
          have hSteps := readDelimitedSteps_le rest
          exact (hHalt.haltsWithin_of_no_randomBit no_randomBit).mono
            (by simp only [budget, List.length_cons]; omega)
      | true =>
          have hRun := runs_bad_tag (true :: rest) (by simp)
          have hHalt : HaltsWith program (true :: rest)
              (rejectedFinish (true :: rest)).outputBits 3 :=
            ⟨_, hRun, rfl, rfl⟩
          exact (hHalt.haltsWithin_of_no_randomBit no_randomBit).mono
            (by simp [budget])

theorem polynomialTime : PolynomialTime program := by
  refine ⟨budget, ?_, haltsWithin⟩
  unfold budget
  exact (PolynomiallyBounded.const 4).mul
    ((PolynomiallyBounded.id).add (PolynomiallyBounded.const 1)) |>.add
      (PolynomiallyBounded.const 8)

/-- The accepted-tag path leaves the first parsed payload and its status on
the output tape; the second delimiter and state are still on the input tape. -/
theorem output_tag_false (rest : List Bool) :
    ({ (readDelimitedFinish [some false] [] rest).resumeAt 19 with halted := true } :
      Configuration).outputBits =
      (scanDelimited rest).field ++ [(scanDelimited rest).complete] := by
  simp [Configuration.outputBits, readDelimitedFinish, Configuration.resumeAt,
    Tape.bits]

theorem output_bad_tag (bits : List Bool) :
    (rejectedFinish bits).outputBits = [false] := by
  simp [rejectedFinish, Configuration.outputBits, Tape.bits, Tape.ofBits]

/-- The first-stage tag and delimiter reader stops on arbitrary retained
tapes. This stronger operational form is used after an outer framed scan. -/
theorem terminates_from_anyTape (input output : Tape) :
    ∃ finish used, used ≤ 10 * (input.cells + output.cells + 1) + 20 ∧
      RunsFor program ({ inputTape := input, outputTape := output } : Configuration)
        finish used ∧ finish.halted = true := by
  let start : Configuration := { inputTape := input, outputTape := output }
  by_cases hTag : input.current = some false
  · let selected : Configuration := { start with pc := 1 }
    let advanced : Configuration :=
      { selected with pc := 2, inputTape := input.moveRight }
    have hBranch : Step program start selected := by
      simp [Step, successors, next, lookup_tag, start, selected,
        hTag, Instruction.next, Configuration.tape]
    have hAdvance : Step program selected advanced := by
      simp [Step, successors, next, lookup_advance, start, selected, advanced,
        Instruction.next, Configuration.updateTape, Configuration.advance]
    obtain ⟨parsed, parseUsed, hParseUsed, parseRun, hParsed⟩ :=
      readDelimited_terminates_from_anyTape input.moveRight output
    obtain ⟨embeddedUsed, hEmbeddedUsed, embedded⟩ :=
      parseRun.withSubroutine_halted tagPrefix readDelimited
        [.halt, .write .output false, .halt] 19
        (by change 0 ≤ 16; omega) rfl hParsed
    have hMiddle : RunsFor program advanced (parsed.resumeAt 19)
        embeddedUsed := by
      simpa [program, tagPrefix, advanced, selected, start,
        Configuration.rebasePc]
        using embedded
    have hRun : RunsFor program start
        { parsed.resumeAt 19 with halted := true }
        (2 + embeddedUsed + 1) :=
      (((RunsFor.zero _).succ hBranch).succ hAdvance).trans hMiddle |>.trans
        (returned_halt parsed)
    have hCells := Tape.cells_moveRight_le input
    refine ⟨_, 2 + embeddedUsed + 1, ?_, hRun, rfl⟩
    omega
  · let selected : Configuration := { start with pc := 20 }
    let written : Configuration :=
      { selected with pc := 21, outputTape := output.write (some false) }
    have hBranch : Step program start selected := by
      cases h : input.current with
      | none =>
          simp [Step, successors, next, lookup_tag, start, selected,
            h, Instruction.next, Configuration.tape]
      | some bit =>
          cases bit with
          | false => exact False.elim (hTag h)
          | true =>
              simp [Step, successors, next, lookup_tag, start, selected,
                h, Instruction.next, Configuration.tape]
    have hWrite : Step program selected written := by
      simp [Step, successors, next, lookup_reject_write, start,
        selected, written, Instruction.next, Configuration.updateTape,
        Configuration.advance]
    have hHalt : Step program written { written with halted := true } := by
      simp [Step, successors, next, lookup_reject_halt,
        written, Instruction.next]
    refine ⟨_, 3, ?_, (((RunsFor.zero _).succ hBranch).succ hWrite).succ hHalt,
      rfl⟩
    omega

theorem scan_delimit_append (field tail : List Bool) :
    scanDelimited (FiniteBitEncoding.delimit field ++ tail) =
      { field := field, tail := tail,
        consumed := FiniteBitEncoding.delimit field, complete := true } := by
  induction field with
  | nil => rfl
  | cons bit rest ih =>
      simp [FiniteBitEncoding.delimit, scanDelimited, ih]

/-- On a canonical choose response, the first native parser leaves the
second field at the input head and the first payload plus success flag on
the output tape. This is a physical-tape handoff, not a decoder call. -/
theorem canonical_handoff (first second state : List Bool) :
    let rest := FiniteBitEncoding.delimit first ++
      FiniteBitEncoding.delimit second ++ state
    let finish : Configuration :=
      { (readDelimitedFinish [some false] [] rest).resumeAt 19 with halted := true }
    finish.inputTape =
      { Tape.ofBits (FiniteBitEncoding.delimit second ++ state) with
        left := (FiniteBitEncoding.delimit first).reverse.map some ++ [some false] } ∧
    finish.outputBits = first ++ [true] := by
  dsimp only
  have hScan := scan_delimit_append first (FiniteBitEncoding.delimit second ++ state)
  constructor
  · simp [readDelimitedFinish, hScan, Configuration.resumeAt, List.append_assoc]
  · rw [output_tag_false]
    simp [List.append_assoc, hScan]

end Machine.ChooseFirstField
