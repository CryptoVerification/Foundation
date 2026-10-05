import Foundation.Machine.BinaryThirdColumnTemplate

namespace Machine.BinaryColumnSlotFill

/-- Write one bit from the input tape into the current output cell, then
advance the output head by three cells. The caller selects the first or
second slot by positioning that head. This fixed code does not inspect the
values in the two other slots. -/
def program : Program :=
  [.branch .input 10 1 3,
   .write .output false, .jump 5,
   .write .output true, .jump 5,
   .moveRight .output, .moveRight .output, .moveRight .output,
   .moveRight .input, .jump 0,
   .halt]

def fillTape (output : Tape) : List Bool → Tape
  | [] => output
  | bit :: rest => fillTape
      (((output.write (some bit)).moveRight).moveRight.moveRight) rest

def firstSlots (first modulus : List Bool) : List Bool :=
  BinaryModularAddition.interleave
    ((first.zip modulus).map fun pair => ((pair.1, false), pair.2))

def fullSlots (first second modulus : List Bool) : List Bool :=
  BinaryModularAddition.interleave ((first.zip second).zip modulus)

/-- The finite three-track arithmetic input has three cells per complete
column; unequal widths retain only the complete zipped columns. -/
theorem fullSlots_length (first second modulus : List Bool) :
    (fullSlots first second modulus).length =
      3 * min (min first.length second.length) modulus.length := by
  have h (columns : List BinaryModularAddition.Column) :
      (BinaryModularAddition.interleave columns).length = 3 * columns.length := by
    induction columns with
    | nil => rfl
    | cons column rest ih => simp [BinaryModularAddition.interleave, ih]; omega
  simpa [fullSlots] using h ((first.zip second).zip modulus)

private theorem ofBits_with_empty_left (bits : List Bool) :
    { Tape.ofBits bits with left := [] } = Tape.ofBits bits := by
  cases bits <;> rfl

/-- The empty first operand track in a modulus template consists of real
false cells, so the same slot writer can populate the exponent first. -/
theorem firstSlots_false (modulus : List Bool) :
    firstSlots (List.replicate modulus.length false) modulus =
      BinaryThirdColumnTemplate.columns modulus := by
  induction modulus with
  | nil => rfl
  | cons bit rest ih =>
      simpa [firstSlots, BinaryThirdColumnTemplate.columns,
        BinaryModularAddition.interleave, List.replicate_succ] using congrArg (fun bits => false :: false :: bit :: bits) ih

/-- With equal-width data, filling the first slot of each modulus template
row leaves the first operand, placeholder, and modulus physically aligned.
The statement describes tape cells; it does not replace the machine run. -/
theorem fillTape_first (first modulus : List Bool)
    (hLength : first.length = modulus.length)
    (before : List (Option Bool)) :
    fillTape
      { Tape.ofBits (BinaryThirdColumnTemplate.columns modulus) with left := before }
      first =
      { left := (firstSlots first modulus).reverse.map some ++ before } := by
  induction first generalizing modulus before with
  | nil =>
      cases modulus with
      | nil => simp [fillTape, firstSlots, BinaryThirdColumnTemplate.columns,
          BinaryModularAddition.interleave, Tape.ofBits]
      | cons bit rest => simp at hLength
  | cons bit rest ih =>
      cases modulus with
      | nil => simp at hLength
      | cons p ps =>
          have hRest : rest.length = ps.length := by simpa using hLength
          have hStep :
              ((({ Tape.ofBits (BinaryThirdColumnTemplate.columns (p :: ps)) with
                   left := before } : Tape).write (some bit)).moveRight).moveRight.moveRight =
                { Tape.ofBits (BinaryThirdColumnTemplate.columns ps) with
                  left := (p :: false :: bit :: []).map some ++ before } := by
            cases ps <;>
              simp [BinaryThirdColumnTemplate.columns,
                BinaryModularAddition.interleave, Tape.ofBits,
                Tape.write, Tape.moveRight]
          simp only [fillTape, hStep]
          rw [ih ps hRest ((p :: false :: bit :: []).map some ++ before)]
          simp [firstSlots, BinaryModularAddition.interleave,
            List.map_append, List.append_assoc]

/-- Starting at the second cell of the first row, the same finite slot
writer replaces every placeholder. The final leading blank is the physical
head position one cell past the completed three-track bitstring. -/
theorem fillTape_second (first second modulus : List Bool)
    (hFirst : first.length = modulus.length)
    (hSecond : second.length = modulus.length)
    (before : List (Option Bool)) :
    fillTape
      (({ Tape.ofBits (firstSlots first modulus) with left := before } : Tape).moveRight)
      second =
      { left := none :: (fullSlots first second modulus).reverse.map some ++ before } := by
  induction second generalizing first modulus before with
  | nil =>
      cases first with
      | nil =>
          cases modulus with
          | nil => simp [fillTape, firstSlots, fullSlots,
              BinaryModularAddition.interleave, Tape.ofBits, Tape.moveRight]
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
              have hStep :
                  ((((({ Tape.ofBits (firstSlots (a :: as) (p :: ps)) with
                       left := before } : Tape).moveRight).write (some bit)).moveRight).moveRight).moveRight =
                    (({ Tape.ofBits (firstSlots as ps) with
                      left := ([a, bit, p].reverse.map some ++ before) } : Tape).moveRight) := by
                cases as <;> cases ps <;>
                  simp [firstSlots, BinaryModularAddition.interleave,
                    Tape.ofBits, Tape.write, Tape.moveRight]
              simp only [fillTape, hStep]
              rw [ih as ps hFirstRest hSecondRest
                ([a, bit, p].reverse.map some ++ before)]
              simp [fullSlots, BinaryModularAddition.interleave,
                List.map_append, List.append_assoc]

private def state (before : List (Option Bool)) (remaining : List Bool)
    (output : Tape) : Configuration :=
  { inputTape := { Tape.ofBits remaining with left := before }, outputTape := output }

private def finish (before : List (Option Bool)) (output : Tape) : Configuration :=
  { pc := 10, inputTape := { left := before }, outputTape := output, halted := true }

private theorem eval_bit (before : List (Option Bool)) (bit : Bool)
    (rest : List Bool) (output : Tape) :
    evalConfigWithin program (state before (bit :: rest) output) 8 =
      PMF.pure (state (some bit :: before) rest
        (((output.write (some bit)).moveRight).moveRight.moveRight)) := by
  cases bit <;> cases rest <;>
    simp [evalConfigWithin, stepPMF, next, program, state,
      Instruction.next, Configuration.advance, Configuration.tape,
      Configuration.updateTape, Tape.ofBits, Tape.moveRight, Tape.write,
      PMF.pure_bind]

private theorem eval_end (before : List (Option Bool)) (output : Tape) :
    evalConfigWithin program (state before [] output) 2 =
      PMF.pure (finish before output) := by
  simp [evalConfigWithin, stepPMF, next, program, state, finish,
    Instruction.next, Configuration.tape, Tape.ofBits, PMF.pure_bind]

/-- The output tape is an arbitrary retained tape. The program overwrites
only the selected slot of each successive three-cell column. -/
theorem eval_context (before : List (Option Bool)) (bits : List Bool)
    (output : Tape) :
    evalConfigWithin program (state before bits output) (8 * bits.length + 2) =
      PMF.pure (finish (bits.reverse.map some ++ before) (fillTape output bits)) := by
  induction bits generalizing before output with
  | nil => simpa [fillTape] using eval_end before output
  | cons bit rest ih =>
      have hTime : 8 * (bit :: rest).length + 2 =
          8 + (8 * rest.length + 2) := by simp; omega
      rw [hTime, evalConfigWithin_add, eval_bit, PMF.pure_bind]
      simpa [fillTape, List.reverse_cons, List.reverse_append,
        List.map_append, List.append_assoc] using
        ih (some bit :: before)
          (((output.write (some bit)).moveRight).moveRight.moveRight)

/-- The first pass fills its own physical output tape, after a modulus
template has been placed there by prior machine steps. -/
theorem eval_first_slots (first modulus : List Bool)
    (hLength : first.length = modulus.length) :
    (evalConfigWithin program
      { inputTape := Tape.ofBits first,
        outputTape := Tape.ofBits (BinaryThirdColumnTemplate.columns modulus) }
      (8 * first.length + 2)).map Configuration.outputBits =
      PMF.pure (firstSlots first modulus) := by
  have hInitial :
      ({ inputTape := Tape.ofBits first,
         outputTape := Tape.ofBits (BinaryThirdColumnTemplate.columns modulus) } : Configuration) =
        state [] first (Tape.ofBits (BinaryThirdColumnTemplate.columns modulus)) := by
    cases first <;> rfl
  have h := eval_context [] first
    (Tape.ofBits (BinaryThirdColumnTemplate.columns modulus))
  have hFill := fillTape_first first modulus hLength []
  simp only [ofBits_with_empty_left] at hFill
  rw [hInitial, h, PMF.pure_map, hFill]
  simp [finish, Configuration.outputBits, Tape.bits]

/-- After the head has been moved to the second cell of the first row,
the second pass returns the exact raw three-track bitstring. -/
theorem eval_full_slots (first second modulus : List Bool)
    (hFirst : first.length = modulus.length)
    (hSecond : second.length = modulus.length) :
    (evalConfigWithin program
      { inputTape := Tape.ofBits second,
        outputTape := (Tape.ofBits (firstSlots first modulus)).moveRight }
      (8 * second.length + 2)).map Configuration.outputBits =
      PMF.pure (fullSlots first second modulus) := by
  have hInitial :
      ({ inputTape := Tape.ofBits second,
         outputTape := (Tape.ofBits (firstSlots first modulus)).moveRight } : Configuration) =
        state [] second ((Tape.ofBits (firstSlots first modulus)).moveRight) := by
    cases second <;> rfl
  have h := eval_context [] second
    ((Tape.ofBits (firstSlots first modulus)).moveRight)
  have hFill := fillTape_second first second modulus hFirst hSecond []
  simp only [ofBits_with_empty_left] at hFill
  rw [hInitial, h, PMF.pure_map, hFill]
  simp [finish, Configuration.outputBits, Tape.bits, List.map_reverse]

theorem haltsWithin (bits : List Bool) :
    HaltsWithin program bits (8 * bits.length + 2) := by
  apply haltsWithin_of_no_timeout_support program bits _
  have hInitial : Configuration.initial bits = state [] bits ({} : Tape) := by
    cases bits <;> rfl
  unfold evalWithin
  rw [hInitial, eval_context, PMF.pure_map]
  simp [finish]

theorem polynomialTime : PolynomialTime program := by
  refine ⟨fun length => 8 * length + 2, ?_, haltsWithin⟩
  exact ((PolynomiallyBounded.const 8).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 2)

/-- Replacing the first track preserves the already populated exponent and
modulus tracks. This is the physical slot-writing recursion, not a tape reload. -/
theorem fillTape_first_full (old first second modulus : List Bool)
    (hOld : old.length = modulus.length)
    (hFirst : first.length = modulus.length)
    (hSecond : second.length = modulus.length)
    (before : List (Option Bool)) :
    fillTape { Tape.ofBits (fullSlots old second modulus) with left := before } first =
      { left := (fullSlots first second modulus).reverse.map some ++ before } := by
  induction first generalizing old second modulus before with
  | nil =>
      have hm : modulus = [] := List.length_eq_zero_iff.mp (by simpa using hFirst.symm)
      subst modulus
      have ho : old = [] := List.length_eq_zero_iff.mp hOld
      have hs : second = [] := List.length_eq_zero_iff.mp hSecond
      subst old
      subst second
      simp [fillTape, fullSlots, BinaryModularAddition.interleave, Tape.ofBits]
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
                  have hStep :
                      ((({ Tape.ofBits (fullSlots (a :: as) (b :: bs) (p :: ps)) with
                          left := before } : Tape).write (some bit)).moveRight).moveRight.moveRight =
                        { Tape.ofBits (fullSlots as bs ps) with
                          left := [some p, some b, some bit] ++ before } := by
                    cases as <;> cases bs <;> cases ps <;>
                      simp [fullSlots, BinaryModularAddition.interleave,
                        Tape.ofBits, Tape.write, Tape.moveRight]
                  simp only [fillTape, hStep]
                  rw [ih as bs ps (by simpa using hOld) (by simpa using hFirst)
                    (by simpa using hSecond) ([some p, some b, some bit] ++ before)]
                  simp [fullSlots, BinaryModularAddition.interleave,
                    List.map_append, List.append_assoc]

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by
  cases tape <;> decide

end Machine.BinaryColumnSlotFill
