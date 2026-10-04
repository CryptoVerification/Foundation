import Foundation.Machine.FramedInput

namespace Machine.CompleteFrameCheck

/-- Validate one complete unary-length frame, including its entire payload
and the absence of trailing bits. Each header bit creates a real counter
cell; each payload bit erases one. Missing delimiters, truncated payloads,
and extra trailing input take the marked rejection exit. -/
def program : Program :=
  [.branch .input 16 5 1,
   .write .output true, .moveRight .output, .moveRight .input, .jump 0,
   .moveRight .input, .moveLeft .output,
   .branch .output 13 8 8,
   .branch .input 16 9 9,
   .erase .output, .moveLeft .output, .moveRight .input, .jump 7,
   .branch .input 14 16 16,
   .halt, .halt,
   .write .output true, .halt]

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

private def counter : Nat → Nat → Tape
  | 0, erased => { right := List.replicate (erased+1) none }
  | count+1, erased =>
      { left := List.replicate count (some true), current := some true,
        right := List.replicate (erased+1) none }

private def consume (before : List (Option Bool)) (count erased : Nat)
    (bits : List Bool) : Configuration :=
  { pc := 7, inputTape := { Tape.ofBits bits with left := before },
    outputTape := counter count erased }

private def rejected (c : Configuration) : Configuration :=
  { c with pc := 17, outputTape := c.outputTape.write (some true), halted := true }

private theorem reject_at (c : Configuration) (hPc : c.pc = 16)
    (hActive : c.halted = false) :
    RunsFor program c (rejected c) 2 := by
  let written : Configuration := { c with pc := 17, outputTape := c.outputTape.write (some true) }
  have hWrite : Step program c written := by
    simp [Step, successors, next, hPc, hActive, program, Instruction.next,
      Configuration.updateTape, Configuration.advance, written]
  have hHalt : Step program written (rejected c) := by
    simp [Step, successors, next, written, rejected, hActive, program, Instruction.next]
  exact ((RunsFor.zero _).succ hWrite).succ hHalt

private theorem consume_one (before : List (Option Bool)) (count erased : Nat)
    (bit : Bool) (rest : List Bool) :
    RunsFor program (consume before (count+1) erased (bit::rest))
      (consume (some bit::before) count (erased+1) rest) 6 := by
  let a := consume before (count+1) erased (bit::rest)
  let b : Configuration := { a with pc := 8 }
  let c : Configuration := { b with pc := 9 }
  let d : Configuration := { c with pc := 10, outputTape := c.outputTape.write none }
  let e : Configuration := { d with pc := 11, outputTape := d.outputTape.moveLeft }
  let f : Configuration := { e with pc := 12, inputTape := e.inputTape.moveRight }
  have h₁ : Step program a b := by
    simp [Step, successors, next, a, b, consume, counter, program,
      Instruction.next, Configuration.tape]
  have h₂ : Step program b c := by
    cases bit <;> simp [Step, successors, next, a, b, c, consume, counter,
      program, Instruction.next, Configuration.tape, Tape.ofBits]
  have h₃ : Step program c d := by
    simp [Step, successors, next, a, b, c, d, consume, program,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h₄ : Step program d e := by
    simp [Step, successors, next, a, b, c, d, e, consume, program,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h₅ : Step program e f := by
    simp [Step, successors, next, a, b, c, d, e, f, consume, program,
      Instruction.next, Configuration.updateTape, Configuration.advance]
  have h₆ : Step program f (consume (some bit::before) count (erased+1) rest) := by
    cases count <;> cases rest <;>
      simp [Step, successors, next, a, b, c, d, e, f, consume, counter,
        program, Instruction.next, Tape.moveLeft, Tape.moveRight, Tape.write,
        Tape.ofBits, List.replicate_succ]
  exact ((((((RunsFor.zero _).succ h₁).succ h₂).succ h₃).succ h₄).succ h₅).succ h₆

/-- The counter-consuming phase rejects every incomplete or overlong
payload, while accepted traces expose the exact original field length. -/
private theorem consume_any (before : List (Option Bool)) (count erased : Nat)
    (bits : List Bool) :
    ∃ target used,
      used ≤ 6 * count + 5 ∧ RunsFor program (consume before count erased bits) target used ∧
      target.halted = true ∧
      (target.outputTape.current = some true ∨
        (bits.length = count ∧ target.inputTape = { left := bits.reverse.map some ++ before } ∧
          target.outputTape = { right := List.replicate (erased+count+1) none })) := by
  induction count generalizing before erased bits with
  | zero =>
    cases bits with
    | nil =>
      let a := consume before 0 erased []
      let b : Configuration := { a with pc := 13 }
      let c : Configuration := { b with pc := 14 }
      let target : Configuration := { c with halted := true }
      have h₁ : Step program a b := by
        simp [Step, successors, next, a, b, consume, counter, program,
          Instruction.next, Configuration.tape]
      have h₂ : Step program b c := by
        simp [Step, successors, next, a, b, c, consume, counter, program,
          Instruction.next, Configuration.tape, Tape.ofBits]
      have h₃ : Step program c target := by
        simp [Step, successors, next, a, b, c, target, consume, program, Instruction.next]
      exact ⟨target, 3, by omega, (((RunsFor.zero _).succ h₁).succ h₂).succ h₃,
        rfl, Or.inr ⟨rfl, by simp [target, c, b, a, consume, Tape.ofBits],
          by simp [target, c, b, a, consume, counter]⟩⟩
    | cons bit rest =>
      let a := consume before 0 erased (bit::rest)
      let b : Configuration := { a with pc := 13 }
      let c : Configuration := { b with pc := 16 }
      have h₁ : Step program a b := by
        simp [Step, successors, next, a, b, consume, counter, program,
          Instruction.next, Configuration.tape]
      have h₂ : Step program b c := by
        cases bit <;> simp [Step, successors, next, a, b, c, consume, counter, program,
          Instruction.next, Configuration.tape, Tape.ofBits]
      exact ⟨rejected c, 4, by omega,
        (((RunsFor.zero _).succ h₁).succ h₂).trans (reject_at c rfl rfl),
        rfl, Or.inl rfl⟩
  | succ count ih =>
    cases bits with
    | nil =>
      let a := consume before (count+1) erased []
      let b : Configuration := { a with pc := 8 }
      let c : Configuration := { b with pc := 16 }
      have h₁ : Step program a b := by
        simp [Step, successors, next, a, b, consume, counter, program,
          Instruction.next, Configuration.tape]
      have h₂ : Step program b c := by
        simp [Step, successors, next, a, b, c, consume, counter, program,
          Instruction.next, Configuration.tape, Tape.ofBits]
      exact ⟨rejected c, 4, by omega,
        (((RunsFor.zero _).succ h₁).succ h₂).trans (reject_at c rfl rfl),
        rfl, Or.inl rfl⟩
    | cons bit rest =>
      obtain ⟨target, used, hUsed, run, hHalt, outcome⟩ :=
        ih (some bit::before) (erased+1) rest
      refine ⟨target, 6+used, by omega,
        (consume_one before count erased bit rest).trans run, hHalt, ?_⟩
      rcases outcome with reject | ⟨hLength, hInput, hOutput⟩
      · exact Or.inl reject
      · refine Or.inr ⟨by simp [hLength], ?_, ?_⟩
        · simpa only [List.reverse_cons, List.map_append, List.map_cons,
            List.map_nil, List.append_assoc, List.cons_append, List.nil_append] using hInput
        · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hOutput

private def header (before : List (Option Bool)) (count : Nat)
    (bits : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits bits with
      left := List.replicate count (some true) ++ before },
    outputTape := { left := List.replicate count (some true) } }

private theorem header_one (before : List (Option Bool)) (count : Nat)
    (rest : List Bool) :
    RunsFor program (header before count (true::rest)) (header before (count+1) rest) 5 := by
  let a := header before count (true::rest)
  let b : Configuration := { a with pc := 1 }
  let c : Configuration := { b with pc := 2, outputTape := b.outputTape.write (some true) }
  let d : Configuration := { c with pc := 3, outputTape := c.outputTape.moveRight }
  let e : Configuration := { d with pc := 4, inputTape := d.inputTape.moveRight }
  have h₁ : Step program a b := by
    simp [Step, successors, next, a, b, header, program, Instruction.next,
      Configuration.tape, Tape.ofBits]
  have h₂ : Step program b c := by
    simp [Step, successors, next, a, b, c, header, program, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h₃ : Step program c d := by
    simp [Step, successors, next, a, b, c, d, header, program, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h₄ : Step program d e := by
    simp [Step, successors, next, a, b, c, d, e, header, program, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h₅ : Step program e (header before (count+1) rest) := by
    cases rest <;> simp [Step, successors, next, a, b, c, d, e, header, program,
      Instruction.next, Tape.moveRight, Tape.write, Tape.ofBits, List.replicate_succ]
  exact (((((RunsFor.zero _).succ h₁).succ h₂).succ h₃).succ h₄).succ h₅

private theorem header_delimiter (before : List (Option Bool)) (count : Nat)
    (rest : List Bool) :
    RunsFor program (header before count (false::rest))
      (consume (some false::List.replicate count (some true) ++ before) count 0 rest) 3 := by
  let a := header before count (false::rest)
  let b : Configuration := { a with pc := 5 }
  let c : Configuration := { b with pc := 6, inputTape := b.inputTape.moveRight }
  have h₁ : Step program a b := by
    simp [Step, successors, next, a, b, header, program, Instruction.next,
      Configuration.tape, Tape.ofBits]
  have h₂ : Step program b c := by
    simp [Step, successors, next, a, b, c, header, program, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have h₃ : Step program c
      (consume (some false::List.replicate count (some true) ++ before) count 0 rest) := by
    cases count <;> cases rest <;> simp [Step, successors, next, a, b, c, header,
      consume, counter, program, Instruction.next, Configuration.updateTape,
      Configuration.advance, Tape.moveLeft, Tape.moveRight, Tape.ofBits,
      List.replicate_succ]
  exact (((RunsFor.zero _).succ h₁).succ h₂).succ h₃

private theorem header_any (before : List (Option Bool)) (count : Nat) (bits : List Bool) :
    ∃ target used,
      used ≤ 11 * bits.length + 6 * count + 8 ∧
      RunsFor program (header before count bits) target used ∧ target.halted = true ∧
      (target.outputTape.current = some true ∨
        ∃ payload, List.replicate count true ++ bits = frame payload ∧
          target.inputTape = { left := (frame payload).reverse.map some ++ before } ∧
          target.outputTape = { right := List.replicate (payload.length+1) none }) := by
  induction bits generalizing count with
  | nil =>
    let a := header before count []
    let b : Configuration := { a with pc := 16 }
    have h₁ : Step program a b := by
      simp [Step, successors, next, a, b, header, program, Instruction.next,
        Configuration.tape, Tape.ofBits]
    exact ⟨rejected b, 3, by simp,
      ((RunsFor.zero _).succ h₁).trans (reject_at b rfl rfl), rfl, Or.inl rfl⟩
  | cons bit rest ih =>
    cases bit with
    | true =>
      obtain ⟨target, used, hUsed, run, hHalt, outcome⟩ := ih (count+1)
      refine ⟨target, 5+used, by simp at *; omega,
        (header_one before count rest).trans run, hHalt, ?_⟩
      rcases outcome with reject | ⟨payload, hFrame, hInput, hOutput⟩
      · exact Or.inl reject
      · refine Or.inr ⟨payload, ?_, hInput, hOutput⟩
        simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using hFrame
    | false =>
      obtain ⟨target, used, hUsed, run, hHalt, outcome⟩ :=
        consume_any (some false::List.replicate count (some true) ++ before) count 0 rest
      refine ⟨target, 3+used, by simp; omega,
        (header_delimiter before count rest).trans run, hHalt, ?_⟩
      rcases outcome with reject | ⟨hLength, hInput, hOutput⟩
      · exact Or.inl reject
      · refine Or.inr ⟨rest, ?_, ?_, ?_⟩
        · simp [frame, hLength]
        · simpa [frame, hLength, List.reverse_append, List.map_append,
            List.reverse_replicate, List.map_replicate, List.append_assoc] using hInput
        · simpa only [Nat.zero_add, hLength] using hOutput

/-- Every finite suffix halts; acceptance certifies exactly one complete
frame. The already consumed outer request is retained on the physical input
tape, and successful counter erasure leaves only outer blank padding. -/
theorem runs_any (before : List (Option Bool)) (bits : List Bool) :
    ∃ target used,
      used ≤ 11 * bits.length + 8 ∧
      RunsFor program { inputTape := { Tape.ofBits bits with left := before } } target used ∧
      target.halted = true ∧
      (target.outputTape.current = some true ∨
        ∃ payload, bits = frame payload ∧
          target.inputTape = { left := (frame payload).reverse.map some ++ before } ∧
          target.outputTape.Equivalent ({} : Tape)) := by
  obtain ⟨target, used, hUsed, run, hHalt, outcome⟩ := header_any before 0 bits
  refine ⟨target, used, by simpa using hUsed, by simpa [header] using run, hHalt, ?_⟩
  rcases outcome with reject | ⟨payload, hFrame, hInput, hOutput⟩
  · exact Or.inl reject
  · refine Or.inr ⟨payload, by simpa using hFrame, hInput, ?_⟩
    rw [hOutput]
    exact Tape.blank_padding_equivalent [] (payload.length+1)

/-- Execute the same verifier on the actual tapes left by the preceding
outer-request checks. Equivalence changes only outer blank padding; no input
or output cells are reset as a machine operation. -/
theorem runs_any_loaded (before : List (Option Bool)) (bits : List Bool)
    (input output : Tape)
    (hInput : input.Equivalent { Tape.ofBits bits with left := before })
    (hOutput : output.Equivalent ({} : Tape)) :
    ∃ target used,
      used ≤ 11 * bits.length + 8 ∧
      RunsFor program { inputTape := input, outputTape := output } target used ∧
      target.halted = true ∧
      (target.outputTape.current = some true ∨
        ∃ payload, bits = frame payload ∧
          target.inputTape.Equivalent { left := (frame payload).reverse.map some ++ before } ∧
          target.outputTape.Equivalent ({} : Tape)) := by
  obtain ⟨canonical, used, hUsed, run, hHalt, outcome⟩ := runs_any before bits
  have hStart :
      ({ inputTape := { Tape.ofBits bits with left := before } } : Configuration).Equivalent
        ({ inputTape := input, outputTape := output } : Configuration) :=
    ⟨rfl, rfl, hInput.symm, hOutput.symm⟩
  obtain ⟨actual, actualRun, hEquivalent⟩ := run.exists_equivalent hStart
  refine ⟨actual, used, hUsed, actualRun, hEquivalent.2.1.symm.trans hHalt, ?_⟩
  rcases outcome with reject | ⟨payload, hFrame, hHistory, hBlank⟩
  · exact Or.inl (hEquivalent.2.2.2.1.symm.trans reject)
  · refine Or.inr ⟨payload, hFrame, ?_, hEquivalent.2.2.2.symm.trans hBlank⟩
    exact hEquivalent.2.2.1.symm.trans (by rw [hHistory]; exact Tape.Equivalent.refl _)

private def accepted (before : List (Option Bool)) (erased : Nat) (bits : List Bool) : Configuration :=
  { pc := 14, inputTape := { left := bits.reverse.map some ++ before },
    outputTape := { right := List.replicate (erased+bits.length+1) none }, halted := true }

private theorem consume_valid (before : List (Option Bool)) (erased : Nat) (bits : List Bool) :
    RunsFor program (consume before bits.length erased bits) (accepted before erased bits)
      (6 * bits.length + 3) := by
  induction bits generalizing before erased with
  | nil =>
    let a := consume before 0 erased []
    let b : Configuration := { a with pc := 13 }
    let c : Configuration := { b with pc := 14 }
    have h₁ : Step program a b := by
      simp [Step, successors, next, a, b, consume, counter, program,
        Instruction.next, Configuration.tape]
    have h₂ : Step program b c := by
      simp [Step, successors, next, a, b, c, consume, counter, program,
        Instruction.next, Configuration.tape, Tape.ofBits]
    have h₃ : Step program c (accepted before erased []) := by
      simp [Step, successors, next, a, b, c, consume, accepted, counter,
        program, Instruction.next, Tape.ofBits]
    exact (((RunsFor.zero _).succ h₁).succ h₂).succ h₃
  | cons bit rest ih =>
    have hRun := (consume_one before rest.length erased bit rest).trans
      (ih (some bit::before) (erased+1))
    have hFinish : accepted (some bit::before) (erased+1) rest = accepted before erased (bit::rest) := by
      simp [accepted, List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [hFinish] at hRun
    convert hRun using 1 <;> simp only [List.length_cons] <;> omega

private theorem header_prefix (before : List (Option Bool)) (count added : Nat)
    (bits : List Bool) :
    RunsFor program (header before count (List.replicate added true ++ bits))
      (header before (count+added) bits) (5 * added) := by
  induction added generalizing count with
  | zero => simp only [List.replicate_zero, List.nil_append, Nat.add_zero, Nat.mul_zero]; exact RunsFor.zero _
  | succ added ih =>
    have hRun := (header_one before count (List.replicate added true ++ bits)).trans (ih (count+1))
    simpa only [List.replicate_succ, List.cons_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm, Nat.mul_add, Nat.mul_one] using hRun

/-- Every correctly framed suffix accepts, leaving its original bits in
input history and physically erased counter cells on the output tape. -/
theorem runs_valid (before : List (Option Bool)) (payload : List Bool) :
    ∃ target used,
      used ≤ 11 * payload.length + 6 ∧
      RunsFor program { inputTape := { Tape.ofBits (frame payload) with left := before } }
        target used ∧ target.halted = true ∧ target.outputTape.current = none ∧
      target.inputTape = { left := (frame payload).reverse.map some ++ before } ∧
      target.outputTape.Equivalent ({} : Tape) := by
  let history := some false::List.replicate payload.length (some true) ++ before
  have hPrefix := header_prefix before 0 payload.length (false::payload)
  simp only [Nat.zero_add] at hPrefix
  have hDelimiter := header_delimiter before payload.length payload
  have hPayload := consume_valid history 0 payload
  have hRun := (hPrefix.trans hDelimiter).trans hPayload
  have hInput : (accepted history 0 payload).inputTape =
      ({ left := (frame payload).reverse.map some ++ before } : Tape) := by
    simp [accepted, history, frame, List.reverse_append, List.map_append, List.append_assoc]
  refine ⟨accepted history 0 payload, 5*payload.length+3+(6*payload.length+3),
    by omega, ?_, rfl, rfl, hInput, ?_⟩
  · simpa only [header, frame, Nat.zero_add, List.replicate_zero, List.nil_append,
      List.append_assoc, List.singleton_append] using hRun
  · simpa only [accepted, Nat.zero_add] using Tape.blank_padding_equivalent [] (payload.length+1)

/-- Correctly framed inputs cannot take the rejecting exit. This forward
statement rules out an always-rejecting implementation that satisfies only
the implication from acceptance to a complete frame. -/
theorem accepted_of_frame {before : List (Option Bool)} {payload : List Bool}
    {target : Configuration} {used : Nat}
    (run : RunsFor program { inputTape := { Tape.ofBits (frame payload) with left := before } } target used)
    (hHalt : target.halted = true) : target.outputTape.current = none := by
  obtain ⟨canonical, steps, _, canonicalRun, canonicalHalt, hCurrent, _, _⟩ := runs_valid before payload
  have hEq := run.halted_finish_eq_of_no_randomBit canonicalRun hHalt canonicalHalt no_randomBit
  rw [hEq]
  exact hCurrent

/-- A complete frame is accepted on the actual loaded tapes, including
outer blank padding left by a preceding counter-erasure stage. -/
theorem accepted_of_frame_loaded (before : List (Option Bool)) (payload : List Bool)
    (input output : Tape)
    (hInput : input.Equivalent { Tape.ofBits (frame payload) with left := before })
    (hOutput : output.Equivalent ({} : Tape))
    {target : Configuration} {used : Nat}
    (run : RunsFor program { inputTape := input, outputTape := output } target used)
    (hHalt : target.halted = true) : target.outputTape.current = none := by
  obtain ⟨canonical, steps, _, canonicalRun, canonicalHalt, hCurrent, _, _⟩ := runs_valid before payload
  have hStart :
      ({ inputTape := { Tape.ofBits (frame payload) with left := before } } : Configuration).Equivalent
        ({ inputTape := input, outputTape := output } : Configuration) :=
    ⟨rfl, rfl, hInput.symm, hOutput.symm⟩
  obtain ⟨actual, actualRun, hEquivalent⟩ := canonicalRun.exists_equivalent hStart
  have hActualHalt : actual.halted = true := hEquivalent.2.1.symm.trans canonicalHalt
  have hSame := run.halted_finish_eq_of_no_randomBit actualRun hHalt hActualHalt no_randomBit
  rw [hSame]
  exact hEquivalent.2.2.2.1.symm.trans hCurrent

/-- Acceptance of this native verifier is equivalent to the existence of
one complete frame; the surrounding consumed request may be retained. -/
theorem accepts_iff_frame (before : List (Option Bool)) (bits : List Bool)
    {target : Configuration} {used : Nat}
    (run : RunsFor program { inputTape := { Tape.ofBits bits with left := before } } target used)
    (hHalt : target.halted = true) :
    target.outputTape.current = none ↔ ∃ payload, bits = frame payload := by
  constructor
  · intro hAccept
    obtain ⟨canonical, steps, _, canonicalRun, canonicalHalt, outcome⟩ := runs_any before bits
    have hEq := run.halted_finish_eq_of_no_randomBit canonicalRun hHalt canonicalHalt no_randomBit
    rcases outcome with reject | ⟨payload, hFrame, _, _⟩
    · have hReject : target.outputTape.current = some true := hEq.symm ▸ reject
      rw [hAccept] at hReject
      cases hReject
    · exact ⟨payload, hFrame⟩
  · rintro ⟨payload, rfl⟩
    exact accepted_of_frame run hHalt

def budget (length : Nat) : Nat := 11 * length + 8

theorem budget_polynomiallyBounded : PolynomiallyBounded budget :=
  ((PolynomiallyBounded.const 11).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 8)

theorem haltsWithin (raw : List Bool) : HaltsWithin program raw (budget raw.length) := by
  obtain ⟨target, used, hUsed, run, hHalt, _⟩ := runs_any [] raw
  have hRun : RunsFor program (Configuration.initial raw) target used := by
    cases raw <;> simpa only [Configuration.initial, Tape.ofBits] using run
  exact hRun.haltsFrom_of_no_randomBit hHalt no_randomBit hUsed

theorem polynomialTime : PolynomialTime program :=
  ⟨budget, budget_polynomiallyBounded, haltsWithin⟩

end Machine.CompleteFrameCheck
