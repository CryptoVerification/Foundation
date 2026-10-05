import Foundation.Machine.BinaryColumnSlotFill

namespace Machine.FramedColumnSlotFill

/-- Skip a unary frame header, then overwrite one cell in each three-cell
output column. The output boundary, rather than an input blank, ends the
payload scan, so a following framed field is left unread. The caller
positions the output head at the first or second slot. -/
def program : Program :=
  [.branch .input 16 1 3,
   .moveRight .input, .jump 5,
   .moveRight .input, .jump 0,
   .branch .output 16 6 6,
   .branch .input 16 7 9,
   .write .output false, .jump 11,
   .write .output true, .jump 11,
   .moveRight .output, .moveRight .output, .moveRight .output,
   .moveRight .input, .jump 5,
   .halt]

private def headerState (before : List (Option Bool))
    (bits : List Bool) (output : Tape) : Configuration :=
  { inputTape := { Tape.ofBits bits with left := before }, outputTape := output }

private def payloadState (before : List (Option Bool))
    (bits : List Bool) (output : Tape) : Configuration :=
  { pc := 5, inputTape := { Tape.ofBits bits with left := before },
    outputTape := output }

private def finish (before : List (Option Bool))
    (bits : List Bool) (output : Tape) : Configuration :=
  { pc := 16, inputTape := { Tape.ofBits bits with left := before },
    outputTape := output, halted := true }

private theorem header_true (before : List (Option Bool))
    (rest : List Bool) (output : Tape) :
    evalConfigWithin program (headerState before (true :: rest) output) 3 =
      PMF.pure (headerState (some true :: before) rest output) := by
  cases rest <;>
    simp [evalConfigWithin, stepPMF, next, program, headerState,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, PMF.pure_bind]

private theorem header_end (before : List (Option Bool))
    (rest : List Bool) (output : Tape) :
    evalConfigWithin program (headerState before (false :: rest) output) 3 =
      PMF.pure (payloadState (some false :: before) rest output) := by
  cases rest <;>
    simp [evalConfigWithin, stepPMF, next, program, headerState, payloadState,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, PMF.pure_bind]

private theorem replicate_insert (count : Nat) (before : List (Option Bool)) :
    List.replicate count (some true) ++ some true :: before =
      some true :: List.replicate count (some true) ++ before := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [List.replicate_succ, List.cons_append] using
        congrArg (List.cons (some true)) ih

/-- The delimiter is consumed by native transitions. The next input cell
is the first payload bit (or the following field when the payload is empty). -/
theorem header (count : Nat) (before : List (Option Bool))
    (payload : List Bool) (output : Tape) :
    evalConfigWithin program
      (headerState before (List.replicate count true ++ false :: payload) output)
      (3 * (count + 1)) =
    PMF.pure (payloadState
      (some false :: List.replicate count (some true) ++ before) payload output) := by
  induction count generalizing before with
  | zero => simpa using header_end before payload output
  | succ count ih =>
      have hTime : 3 * (count + 1 + 1) = 3 + 3 * (count + 1) := by omega
      rw [hTime, evalConfigWithin_add]
      simp only [List.replicate_succ, List.cons_append, header_true, PMF.pure_bind]
      have hIH := ih (some true :: before)
      simp only [List.cons_append] at hIH ⊢
      rw [replicate_insert count before] at hIH
      exact hIH

private theorem payload_bit (before : List (Option Bool))
    (bit : Bool) (rest : List Bool) (output : Tape)
    (hCurrent : output.current ≠ none) :
    evalConfigWithin program (payloadState before (bit :: rest) output) 9 =
      PMF.pure (payloadState (some bit :: before) rest
        (((output.write (some bit)).moveRight).moveRight.moveRight)) := by
  cases output with
  | mk left current right =>
    cases current with
    | none => contradiction
    | some present =>
        cases present <;> cases bit <;> cases rest <;>
          simp [evalConfigWithin, stepPMF, next, program, payloadState,
            Instruction.next, Configuration.advance, Configuration.tape,
            Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write,
            PMF.pure_bind]

private theorem payload_end (before : List (Option Bool))
    (bits : List Bool) (output : Tape) (hCurrent : output.current = none) :
    evalConfigWithin program (payloadState before bits output) 2 =
      PMF.pure (finish before bits output) := by
  cases output with
  | mk left current right =>
    cases current with
    | none =>
        cases bits <;>
          simp [evalConfigWithin, stepPMF, next, program, payloadState, finish,
            Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]
    | some present => contradiction

private theorem payload_input_end (before : List (Option Bool))
    (output : Tape) (hCurrent : output.current ≠ none) :
    evalConfigWithin program (payloadState before [] output) 3 =
      PMF.pure (finish before [] output) := by
  cases output with
  | mk left current right =>
    cases current with
    | none => contradiction
    | some present =>
        cases present <;>
          simp [evalConfigWithin, stepPMF, next, program, payloadState,
            finish, Instruction.next, Configuration.tape, Tape.ofBits,
            PMF.pure_bind]

private theorem eval_halted (c : Configuration) (steps : Nat)
    (h : c.halted = true) :
    evalConfigWithin program c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]

private theorem eval_extend {start finish : Configuration} {steps : Nat}
    (h : evalConfigWithin program start steps = PMF.pure finish)
    (hHalted : finish.halted = true) (extra : Nat) :
    evalConfigWithin program start (steps + extra) = PMF.pure finish := by
  rw [evalConfigWithin_add, h, PMF.pure_bind, eval_halted finish extra hHalted]

/-- Regardless of the values in the two tapes, the payload loop consumes at
most one input bit per nine transitions. A blank on either tape halts it. -/
private theorem payload_all (before : List (Option Bool))
    (bits : List Bool) (output : Tape) :
    ∃ finish remaining before',
      evalConfigWithin program (payloadState before bits output)
        (9 * bits.length + 3) = PMF.pure finish ∧ finish.halted = true ∧
      finish.inputTape = { Tape.ofBits remaining with left := before' } ∧
      remaining.length ≤ bits.length := by
  induction bits generalizing before output with
  | nil =>
      by_cases hCurrent : output.current = none
      · refine ⟨finish before [] output, [], before, ?_, rfl, rfl, by simp⟩
        change evalConfigWithin program (payloadState before [] output) 3 = _
        have h := payload_end before [] output hCurrent
        simpa only [show (3 : Nat) = 2 + 1 by omega] using
          eval_extend h rfl 1
      · exact ⟨finish before [] output, [], before,
          by simpa using payload_input_end before output hCurrent,
          rfl, rfl, by simp⟩
  | cons bit rest ih =>
      by_cases hCurrent : output.current = none
      · refine ⟨finish before (bit :: rest) output, bit :: rest,
          before, ?_, rfl, rfl, by simp⟩
        have h := payload_end before (bit :: rest) output hCurrent
        simpa only [show 9 * (bit :: rest).length + 3 =
          2 + (9 * (bit :: rest).length + 1) by omega] using
          eval_extend h rfl (9 * (bit :: rest).length + 1)
      · obtain ⟨after, remaining, before', hAfter, hHalted,
          hInput, hLength⟩ := ih (some bit :: before)
          (((output.write (some bit)).moveRight).moveRight.moveRight)
        refine ⟨after, remaining, before', ?_, hHalted, hInput, ?_⟩
        have hTime : 9 * (bit :: rest).length + 3 =
            9 + (9 * rest.length + 3) := by simp; omega
        rw [hTime, evalConfigWithin_add,
          payload_bit before bit rest output hCurrent, PMF.pure_bind]
        exact hAfter
        simp at hLength ⊢
        omega

/-- The payload entry is usable by callers whose instance fields have no
individual frame header. It reads at most the finite input suffix and leaves
all trailing fields on the same physical input tape. -/
theorem runs_payload_any (before : List (Option Bool))
    (bits : List Bool) (output : Tape) :
    ∃ target remaining before' used,
      used ≤ 9 * bits.length + 3 ∧
      RunsFor program
        (payloadState before bits output) target used ∧
      target.halted = true ∧
      target.inputTape = { Tape.ofBits remaining with left := before' } ∧
      remaining.length ≤ bits.length := by
  obtain ⟨target, remaining, before', hEval, hHalt, hInput, hLength⟩ :=
    payload_all before bits output
  have hSupport : target ∈
      (evalConfigWithin program (payloadState before bits output)
        (9 * bits.length + 3)).support := by
    rw [hEval]
    simp
  obtain ⟨used, hUsed, run⟩ :=
    ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le
  exact ⟨target, remaining, before', used, hUsed, run, hHalt, hInput, hLength⟩

private theorem header_empty (before : List (Option Bool)) (output : Tape) :
    evalConfigWithin program (headerState before [] output) 2 =
      PMF.pure (finish before [] output) := by
  simp [evalConfigWithin, stepPMF, next, program, headerState, finish,
    Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]

/-- The unary scan and output-bounded payload scan halt on every finite
physical input and output tape. This bound refers to the unread input suffix;
the output contents are arbitrary and need no validity assumption. -/
theorem all_context_suffix (before : List (Option Bool)) (bits : List Bool)
    (output : Tape) :
    ∃ finish remaining before',
      evalConfigWithin program (headerState before bits output)
        (12 * bits.length + 3) = PMF.pure finish ∧ finish.halted = true ∧
      finish.inputTape = { Tape.ofBits remaining with left := before' } ∧
      remaining.length ≤ bits.length := by
  induction bits generalizing before with
  | nil =>
      refine ⟨finish before [] output, [], before, ?_, rfl, rfl, by simp⟩
      change evalConfigWithin program (headerState before [] output) 3 = _
      simpa only [show (3 : Nat) = 2 + 1 by omega] using
        eval_extend (header_empty before output) rfl 1
  | cons bit rest ih =>
      cases bit with
      | true =>
          obtain ⟨after, remaining, before', hAfter, hHalted,
            hInput, hLength⟩ := ih (some true :: before)
          refine ⟨after, remaining, before', ?_, hHalted, hInput, ?_⟩
          have hTime : 12 * (true :: rest).length + 3 =
              (3 + (12 * rest.length + 3)) + 9 := by simp; omega
          rw [hTime]
          apply eval_extend _ hHalted 9
          rw [evalConfigWithin_add, header_true, PMF.pure_bind]
          exact hAfter
          simp at hLength ⊢
          omega
      | false =>
          obtain ⟨after, remaining, before', hAfter, hHalted,
            hInput, hLength⟩ :=
            payload_all (some false :: before) rest output
          refine ⟨after, remaining, before', ?_, hHalted, hInput, ?_⟩
          have hTime : 12 * (false :: rest).length + 3 =
              (3 + (9 * rest.length + 3)) + (3 * rest.length + 9) := by simp; omega
          rw [hTime]
          apply eval_extend _ hHalted (3 * rest.length + 9)
          rw [evalConfigWithin_add, header_end, PMF.pure_bind]
          exact hAfter
          simp at hLength ⊢
          omega

theorem all_context (before : List (Option Bool)) (bits : List Bool)
    (output : Tape) :
    ∃ finish,
      evalConfigWithin program (headerState before bits output)
        (12 * bits.length + 3) = PMF.pure finish ∧ finish.halted = true := by
  obtain ⟨finish, _, _, hEval, hHalt, _, _⟩ :=
    all_context_suffix before bits output
  exact ⟨finish, hEval, hHalt⟩

/-- A framed field fills exactly the available three-cell columns and then
stops at the physical blank after the final column, even when another frame
follows on the input tape. -/
theorem payload_first (first modulus tail : List Bool)
    (hLength : first.length = modulus.length)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin program
      (payloadState beforeInput (first ++ tail)
        { Tape.ofBits (BinaryThirdColumnTemplate.columns modulus) with
          left := beforeOutput })
      (9 * first.length + 2) =
    PMF.pure (finish (first.reverse.map some ++ beforeInput) tail
      { left := (BinaryColumnSlotFill.firstSlots first modulus).reverse.map some ++
          beforeOutput }) := by
  induction first generalizing modulus beforeInput beforeOutput with
  | nil =>
      cases modulus with
      | nil =>
          simpa [BinaryThirdColumnTemplate.columns,
            BinaryColumnSlotFill.firstSlots,
            BinaryModularAddition.interleave, Tape.ofBits] using
            payload_end beforeInput tail ({ left := beforeOutput } : Tape) rfl
      | cons bit rest => simp at hLength
  | cons bit rest ih =>
      cases modulus with
      | nil => simp at hLength
      | cons p ps =>
          have hRest : rest.length = ps.length := by simpa using hLength
          have hCurrent :
              ({ Tape.ofBits (BinaryThirdColumnTemplate.columns (p :: ps)) with
                 left := beforeOutput } : Tape).current ≠ none := by
            simp [BinaryThirdColumnTemplate.columns,
              BinaryModularAddition.interleave, Tape.ofBits]
          have hStep :
              ((({ Tape.ofBits (BinaryThirdColumnTemplate.columns (p :: ps)) with
                   left := beforeOutput } : Tape).write (some bit)).moveRight).moveRight.moveRight =
                { Tape.ofBits (BinaryThirdColumnTemplate.columns ps) with
                  left := (p :: false :: bit :: []).map some ++ beforeOutput } := by
            cases ps <;>
              simp [BinaryThirdColumnTemplate.columns,
                BinaryModularAddition.interleave, Tape.ofBits,
                Tape.write, Tape.moveRight]
          have hTime : 9 * (bit :: rest).length + 2 =
              9 + (9 * rest.length + 2) := by simp; omega
          rw [hTime, evalConfigWithin_add]
          simp only [List.cons_append, payload_bit _ _ _ _ hCurrent, PMF.pure_bind,
            hStep]
          convert ih ps hRest (some bit :: beforeInput)
            ((p :: false :: bit :: []).map some ++ beforeOutput) using 1;
            simp [BinaryColumnSlotFill.firstSlots,
              BinaryModularAddition.interleave, List.reverse_cons,
              List.map_append, List.append_assoc]

/-- A complete framed first operand is consumed from the physical input
tape. The following frame remains at the input head. -/
theorem framed_first (first modulus tail : List Bool)
    (hLength : first.length = modulus.length)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin program
      (headerState beforeInput (frame first ++ tail)
        { Tape.ofBits (BinaryThirdColumnTemplate.columns modulus) with
          left := beforeOutput })
      (3 * (first.length + 1) + (9 * first.length + 2)) =
    PMF.pure (finish
      (first.reverse.map some ++
        some false :: List.replicate first.length (some true) ++ beforeInput)
      tail
      { left := (BinaryColumnSlotFill.firstSlots first modulus).reverse.map some ++
          beforeOutput }) := by
  have hFrame : frame first ++ tail =
      List.replicate first.length true ++ false :: (first ++ tail) := by
    simp [frame, List.append_assoc]
  rw [hFrame]
  rw [evalConfigWithin_add]
  rw [header, PMF.pure_bind, payload_first first modulus tail hLength]
  simp [List.append_assoc]

theorem framed_first_explicit (first modulus tail : List Bool)
    (hLength : first.length = modulus.length)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin program
      { inputTape := { Tape.ofBits (frame first ++ tail) with left := beforeInput },
        outputTape := { Tape.ofBits (BinaryThirdColumnTemplate.columns modulus) with
          left := beforeOutput } }
      (3 * (first.length + 1) + (9 * first.length + 2)) =
    PMF.pure
      { pc := 16,
        inputTape := { Tape.ofBits tail with
          left := first.reverse.map some ++
            some false :: List.replicate first.length (some true) ++ beforeInput },
        outputTape :=
          { left := (BinaryColumnSlotFill.firstSlots first modulus).reverse.map some ++
              beforeOutput },
        halted := true } := by
  simpa only [headerState, finish] using
    framed_first first modulus tail hLength beforeInput beforeOutput

/-- The same fixed code fills the second cell of each already populated
three-cell column. The first operand and modulus cells are preserved. -/
theorem payload_second (first second modulus tail : List Bool)
    (hFirst : first.length = modulus.length)
    (hSecond : second.length = modulus.length)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin program
      (payloadState beforeInput (second ++ tail)
        (({ Tape.ofBits (BinaryColumnSlotFill.firstSlots first modulus) with
            left := beforeOutput } : Tape).moveRight))
      (9 * second.length + 2) =
    PMF.pure (finish (second.reverse.map some ++ beforeInput) tail
      { left := none ::
          (BinaryColumnSlotFill.fullSlots first second modulus).reverse.map some ++
            beforeOutput }) := by
  induction second generalizing first modulus beforeInput beforeOutput with
  | nil =>
      cases first with
      | nil =>
          cases modulus with
          | nil =>
              simpa [BinaryColumnSlotFill.firstSlots,
                BinaryColumnSlotFill.fullSlots,
                BinaryModularAddition.interleave, Tape.ofBits, Tape.moveRight]
                using payload_end beforeInput tail
                  (({ left := beforeOutput } : Tape).moveRight) rfl
          | cons p ps => simp at hFirst
      | cons a as => simp at hFirst hSecond; omega
  | cons bit rest ih =>
      cases first with
      | nil => simp at hFirst hSecond; omega
      | cons a as =>
          cases modulus with
          | nil => simp at hFirst
          | cons p ps =>
              have hFirstRest : as.length = ps.length := by simpa using hFirst
              have hSecondRest : rest.length = ps.length := by simpa using hSecond
              have hCurrent :
                  (({ Tape.ofBits
                      (BinaryColumnSlotFill.firstSlots (a :: as) (p :: ps)) with
                      left := beforeOutput } : Tape).moveRight).current ≠ none := by
                simp [BinaryColumnSlotFill.firstSlots,
                  BinaryModularAddition.interleave, Tape.ofBits, Tape.moveRight]
              have hStep :
                  ((((({ Tape.ofBits
                       (BinaryColumnSlotFill.firstSlots (a :: as) (p :: ps)) with
                       left := beforeOutput } : Tape).moveRight).write
                       (some bit)).moveRight).moveRight).moveRight =
                    (({ Tape.ofBits (BinaryColumnSlotFill.firstSlots as ps) with
                      left := ([a, bit, p].reverse.map some ++ beforeOutput) } : Tape).moveRight) := by
                cases as <;> cases ps <;>
                  simp [BinaryColumnSlotFill.firstSlots,
                    BinaryModularAddition.interleave,
                    Tape.ofBits, Tape.write, Tape.moveRight]
              have hTime : 9 * (bit :: rest).length + 2 =
                  9 + (9 * rest.length + 2) := by simp; omega
              rw [hTime, evalConfigWithin_add]
              simp only [List.cons_append, payload_bit _ _ _ _ hCurrent,
                PMF.pure_bind, hStep]
              convert ih as ps hFirstRest hSecondRest (some bit :: beforeInput)
                ([a, bit, p].reverse.map some ++ beforeOutput) using 1;
                simp [BinaryColumnSlotFill.fullSlots,
                  BinaryModularAddition.interleave, List.reverse_cons,
                  List.map_append, List.append_assoc]

/-- The payload loop also replaces an existing first track. The already
populated exponent and modulus are preserved, and an arbitrary following
input suffix is left unread. This permits two powers using one saved scalar. -/
theorem payload_replace_first (old first second modulus tail : List Bool)
    (hOld : old.length = modulus.length) (hFirst : first.length = modulus.length)
    (hSecond : second.length = modulus.length)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin program
      (payloadState beforeInput (first ++ tail)
        {Tape.ofBits (BinaryColumnSlotFill.fullSlots old second modulus) with left := beforeOutput})
      (9*first.length+2) =
    PMF.pure (finish (first.reverse.map some ++ beforeInput) tail
      {left := (BinaryColumnSlotFill.fullSlots first second modulus).reverse.map some ++ beforeOutput}) := by
  induction first generalizing old second modulus beforeInput beforeOutput with
  | nil =>
    cases modulus with
    | cons p ps => simp at hFirst
    | nil =>
      cases old with
      | cons a as => simp at hOld
      | nil =>
        cases second with
        | cons b bs => simp at hSecond
        | nil =>
          simpa [BinaryColumnSlotFill.fullSlots, BinaryModularAddition.interleave,
            Tape.ofBits] using payload_end beforeInput tail ({left := beforeOutput} : Tape) rfl
  | cons bit rest ih =>
    cases modulus with
    | nil => simp at hFirst
    | cons p ps =>
      cases old with
      | nil => simp at hOld
      | cons a as =>
        cases second with
        | nil => simp at hSecond
        | cons b bs =>
          have hCurrent : ({Tape.ofBits (BinaryColumnSlotFill.fullSlots (a::as) (b::bs) (p::ps)) with left := beforeOutput} : Tape).current ≠ none := by
            simp [BinaryColumnSlotFill.fullSlots, BinaryModularAddition.interleave, Tape.ofBits]
          have hStep : (((({Tape.ofBits (BinaryColumnSlotFill.fullSlots (a::as) (b::bs) (p::ps)) with left := beforeOutput} : Tape).write (some bit)).moveRight).moveRight).moveRight =
              {Tape.ofBits (BinaryColumnSlotFill.fullSlots as bs ps) with left := [some p, some b, some bit] ++ beforeOutput} := by
            cases as <;> cases bs <;> cases ps <;>
              simp [BinaryColumnSlotFill.fullSlots, BinaryModularAddition.interleave,
                Tape.ofBits, Tape.write, Tape.moveRight]
          have time : 9*(bit::rest).length+2 = 9+(9*rest.length+2) := by simp; omega
          rw [time, evalConfigWithin_add]
          simp only [List.cons_append, payload_bit _ _ _ _ hCurrent, PMF.pure_bind, hStep]
          convert ih as bs ps (by simpa using hOld) (by simpa using hFirst)
            (by simpa using hSecond) (some bit::beforeInput)
            ([some p, some b, some bit] ++ beforeOutput) using 1 <;>
              simp [BinaryColumnSlotFill.fullSlots, BinaryModularAddition.interleave,
                List.reverse_cons, List.map_append, List.append_assoc]

/-- An unframed exponent is copied into the second arithmetic track by
entering the existing finite code at its payload loop. The following generator
and response fields remain unread. -/
theorem runs_payload_second (first exponent modulus tail : List Bool)
    (hFirst : first.length = modulus.length)
    (hExponent : exponent.length = modulus.length)
    (beforeInput beforeOutput : List (Option Bool)) :
    ∃ used, used ≤ 9 * exponent.length + 2 ∧
      RunsFor program
        (payloadState beforeInput (exponent ++ tail)
          ({ Tape.ofBits (BinaryColumnSlotFill.firstSlots first modulus) with
            left := beforeOutput } : Tape).moveRight)
        (finish (exponent.reverse.map some ++ beforeInput) tail
          { left := none ::
            (BinaryColumnSlotFill.fullSlots first exponent modulus).reverse.map some ++
              beforeOutput }) used := by
  have hEval := payload_second first exponent modulus tail hFirst hExponent
    beforeInput beforeOutput
  have hSupport :
      (finish (exponent.reverse.map some ++ beforeInput) tail
        { left := none ::
          (BinaryColumnSlotFill.fullSlots first exponent modulus).reverse.map some ++
            beforeOutput }) ∈
      (evalConfigWithin program
        (payloadState beforeInput (exponent ++ tail)
          ({ Tape.ofBits (BinaryColumnSlotFill.firstSlots first modulus) with
            left := beforeOutput } : Tape).moveRight)
        (9 * exponent.length + 2)).support := by
    rw [hEval]
    simp
  exact ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSupport).toRunsFor_le

/-- Starting from the retained modulus template, copy the fixed-width
instance exponent into the second track, leaving the candidate track empty. -/
theorem runs_payload_exponent (exponent modulus tail : List Bool)
    (hExponent : exponent.length = modulus.length)
    (beforeInput beforeOutput : List (Option Bool)) :
    ∃ used, used ≤ 9 * exponent.length + 2 ∧
      RunsFor program
        (payloadState beforeInput (exponent ++ tail)
          ({ Tape.ofBits (BinaryThirdColumnTemplate.columns modulus) with
            left := beforeOutput } : Tape).moveRight)
        (finish (exponent.reverse.map some ++ beforeInput) tail
          { left := none ::
            (BinaryColumnSlotFill.fullSlots (List.replicate modulus.length false)
              exponent modulus).reverse.map some ++ beforeOutput }) used := by
  simpa only [BinaryColumnSlotFill.firstSlots_false] using
    runs_payload_second (List.replicate modulus.length false) exponent modulus tail
      (by simp) hExponent beforeInput beforeOutput

theorem framed_second (first second modulus tail : List Bool)
    (hFirst : first.length = modulus.length)
    (hSecond : second.length = modulus.length)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin program
      (headerState beforeInput (frame second ++ tail)
        (({ Tape.ofBits (BinaryColumnSlotFill.firstSlots first modulus) with
            left := beforeOutput } : Tape).moveRight))
      (3 * (second.length + 1) + (9 * second.length + 2)) =
    PMF.pure (finish
      (second.reverse.map some ++
        some false :: List.replicate second.length (some true) ++ beforeInput)
      tail
      { left := none ::
          (BinaryColumnSlotFill.fullSlots first second modulus).reverse.map some ++
            beforeOutput }) := by
  have hFrame : frame second ++ tail =
      List.replicate second.length true ++ false :: (second ++ tail) := by
    simp [frame, List.append_assoc]
  rw [hFrame, evalConfigWithin_add, header, PMF.pure_bind,
    payload_second first second modulus tail hFirst hSecond]
  simp [List.append_assoc]

theorem framed_second_explicit (first second modulus tail : List Bool)
    (hFirst : first.length = modulus.length)
    (hSecond : second.length = modulus.length)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin program
      { inputTape := { Tape.ofBits (frame second ++ tail) with left := beforeInput },
        outputTape :=
          (({ Tape.ofBits (BinaryColumnSlotFill.firstSlots first modulus) with
            left := beforeOutput } : Tape).moveRight) }
      (3 * (second.length + 1) + (9 * second.length + 2)) =
    PMF.pure
      { pc := 16,
        inputTape := { Tape.ofBits tail with
          left := second.reverse.map some ++
            some false :: List.replicate second.length (some true) ++ beforeInput },
        outputTape :=
          { left := none ::
              (BinaryColumnSlotFill.fullSlots first second modulus).reverse.map some ++
                beforeOutput },
        halted := true } := by
  simpa only [headerState, finish] using
    framed_second first second modulus tail hFirst hSecond beforeInput beforeOutput

/-- The third slot can be filled from the first fixed-width field of an
instance frame. Its two leading false cells remain in every column. -/
theorem payload_third (modulus tail : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) :
    evalConfigWithin program
      (payloadState beforeInput (modulus ++ tail)
        (({ Tape.ofBits (BinaryThirdColumnTemplate.columns
            (List.replicate modulus.length false)) with
            left := beforeOutput } : Tape).moveRight.moveRight))
      (9 * modulus.length + 2) =
    PMF.pure (finish (modulus.reverse.map some ++ beforeInput) tail
      { left := none :: none ::
          (BinaryThirdColumnTemplate.columns modulus).reverse.map some ++
            beforeOutput }) := by
  induction modulus generalizing beforeInput beforeOutput with
  | nil =>
      simpa [BinaryThirdColumnTemplate.columns,
        BinaryModularAddition.interleave, Tape.ofBits, Tape.moveRight]
        using payload_end beforeInput tail
          ((({ left := beforeOutput } : Tape).moveRight).moveRight) rfl
  | cons bit rest ih =>
      have hCurrent :
          (({ Tape.ofBits (BinaryThirdColumnTemplate.columns
              (List.replicate (bit :: rest).length false)) with
              left := beforeOutput } : Tape).moveRight.moveRight).current ≠ none := by
        simp [BinaryThirdColumnTemplate.columns,
          BinaryModularAddition.interleave, Tape.ofBits, Tape.moveRight,
          List.replicate_succ]
      have hStep :
          ((((({ Tape.ofBits (BinaryThirdColumnTemplate.columns
              (List.replicate (bit :: rest).length false)) with
              left := beforeOutput } : Tape).moveRight.moveRight).write
              (some bit)).moveRight).moveRight).moveRight =
            (({ Tape.ofBits (BinaryThirdColumnTemplate.columns
                (List.replicate rest.length false)) with
                left := ([false, false, bit].reverse.map some ++ beforeOutput) } :
                Tape).moveRight.moveRight) := by
        cases rest <;>
          simp [BinaryThirdColumnTemplate.columns,
            BinaryModularAddition.interleave, Tape.ofBits,
            Tape.write, Tape.moveRight, List.replicate_succ]
      have hTime : 9 * (bit :: rest).length + 2 =
          9 + (9 * rest.length + 2) := by simp; omega
      rw [hTime, evalConfigWithin_add]
      simp only [List.cons_append, payload_bit _ _ _ _ hCurrent,
        PMF.pure_bind, hStep]
      convert ih (some bit :: beforeInput)
        ([false, false, bit].reverse.map some ++ beforeOutput) using 1;
        simp [BinaryThirdColumnTemplate.columns,
          BinaryModularAddition.interleave, List.reverse_cons,
          List.map_append, List.append_assoc]

/-- For an instance frame whose first fixed-width field is the modulus, the
unary frame header is consumed and only that first field is copied into the
third column slot. The remaining instance fields stay on the input tape. -/
theorem framed_modulus (modulus trailingFields rest : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) :
    let instanceBits := modulus ++ trailingFields
    evalConfigWithin program
      (headerState beforeInput (frame instanceBits ++ rest)
        (({ Tape.ofBits (BinaryThirdColumnTemplate.columns
            (List.replicate modulus.length false)) with
            left := beforeOutput } : Tape).moveRight.moveRight))
      (3 * (instanceBits.length + 1) + (9 * modulus.length + 2)) =
    PMF.pure (finish
      (modulus.reverse.map some ++
        some false :: List.replicate instanceBits.length (some true) ++ beforeInput)
      (trailingFields ++ rest)
      { left := none :: none ::
          (BinaryThirdColumnTemplate.columns modulus).reverse.map some ++
            beforeOutput }) := by
  dsimp only
  have hFrame : frame (modulus ++ trailingFields) ++ rest =
      List.replicate (modulus ++ trailingFields).length true ++
        false :: (modulus ++ (trailingFields ++ rest)) := by
    simp [frame, List.append_assoc]
  rw [hFrame, evalConfigWithin_add, header, PMF.pure_bind,
    payload_third modulus (trailingFields ++ rest)]
  simp [List.append_assoc]

/-- Explicit tape form of `framed_modulus`, for embedding into a larger
machine program without exposing its private state constructors. -/
theorem framed_modulus_explicit (modulus trailingFields rest : List Bool)
    (beforeInput beforeOutput : List (Option Bool)) :
    let instanceBits := modulus ++ trailingFields
    evalConfigWithin program
      { inputTape := { Tape.ofBits (frame instanceBits ++ rest) with left := beforeInput },
        outputTape :=
          (({ Tape.ofBits (BinaryThirdColumnTemplate.columns
            (List.replicate modulus.length false)) with
            left := beforeOutput } : Tape).moveRight.moveRight) }
      (3 * (instanceBits.length + 1) + (9 * modulus.length + 2)) =
    PMF.pure
      { pc := 16,
        inputTape :=
          { Tape.ofBits (trailingFields ++ rest) with
            left := modulus.reverse.map some ++
              some false :: List.replicate instanceBits.length (some true) ++ beforeInput },
        outputTape :=
          { left := none :: none ::
              (BinaryThirdColumnTemplate.columns modulus).reverse.map some ++ beforeOutput },
        halted := true } := by
  simpa only [headerState, finish] using
    framed_modulus modulus trailingFields rest beforeInput beforeOutput

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits (12 * bits.length + 3) := by
  obtain ⟨target, hEval, hHalted⟩ := all_context [] bits ({} : Tape)
  apply haltsWithin_of_no_timeout_support program bits _
  have hInitial : Configuration.initial bits = headerState [] bits ({} : Tape) := by
    cases bits <;> rfl
  unfold evalWithin
  rw [hInitial, hEval, PMF.pure_map]
  simp [hHalted]

theorem polynomialTime : PolynomialTime program := by
  refine ⟨fun length => 12 * length + 3, ?_, haltsWithin⟩
  exact ((PolynomiallyBounded.const 12).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 3)

end Machine.FramedColumnSlotFill
