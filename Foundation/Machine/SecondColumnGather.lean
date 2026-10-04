import Foundation.Machine.BinaryColumnSlotFill
import Foundation.Machine.GuardedTrace

namespace Machine.SecondColumnGather

/-- Read each real three-cell column and copy its middle cell. The counter
variant writes one true cell per complete column, retaining the same width
for postprocessing after the random sampler returns. -/
private def code (counter : Bool) : Program :=
  [.branch .input 13 1 1, .moveRight .input, .branch .input 13 3 6,
   .write .output counter, .moveRight .output, .jump 9,
   .write .output true, .moveRight .output, .jump 9,
   .moveRight .input, .branch .input 13 11 11, .moveRight .input, .jump 0, .halt]

def program : Program := code false
def counterProgram : Program := code true

private def selected (counter : Bool) (columns : List BinaryModularAddition.Column) : List Bool :=
  columns.map (fun column => if counter then true else column.1.2)

private def start (before written : List (Option Bool)) (bits : List Bool) : Configuration :=
  { inputTape := { Tape.ofBits bits with left := before }
    outputTape := { left := written } }
private def finish (before written : List (Option Bool)) : Configuration :=
  { pc := 13
    halted := true
    inputTape := { left := before }
    outputTape := { left := written } }

private theorem column_runs (counter : Bool) (a b p : Bool) (rest : List Bool)
    (before written : List (Option Bool)) :
    RunsFor (code counter) (start before written (a::b::p::rest))
      (start (some p::some b::some a::before)
        (some (if counter then true else b)::written) rest) 10 := by
  let s₀ := start before written (a::b::p::rest)
  let s₁ := { s₀ with pc := 1 }
  let s₂ := { s₁ with pc := 2, inputTape := s₁.inputTape.moveRight }
  let s₃ := { s₂ with pc := if b then 6 else 3 }
  let s₄ := { s₃ with pc := if b then 7 else 4, outputTape := s₃.outputTape.write (some (if counter then true else b)) }
  let s₅ := { s₄ with pc := if b then 8 else 5, outputTape := s₄.outputTape.moveRight }
  let s₆ := { s₅ with pc := 9 }
  let s₇ := { s₆ with pc := 10, inputTape := s₆.inputTape.moveRight }
  let s₈ := { s₇ with pc := 11 }
  let s₉ := { s₈ with pc := 12, inputTape := s₈.inputTape.moveRight }
  have r₁ : Step (code counter) s₀ s₁ := by
    cases a <;> simp [Step, successors, next, code, s₀, s₁, start, Tape.ofBits,
      Instruction.next, Configuration.tape]
  have r₂ : Step (code counter) s₁ s₂ := by
    simp [Step, successors, next, code, s₀, s₁, s₂, start, Instruction.next,
      Configuration.updateTape, Configuration.advance]
  have r₃ : Step (code counter) s₂ s₃ := by
    cases b <;> simp [Step, successors, next, code, s₀, s₁, s₂, s₃, start,
      Tape.ofBits, Tape.moveRight, Instruction.next, Configuration.tape]
  have r₄ : Step (code counter) s₃ s₄ := by
    cases b <;> cases counter <;> simp [Step, successors, next, code, s₀, s₁, s₂, s₃, s₄,
      start, Instruction.next, Configuration.updateTape, Configuration.advance]
  have r₅ : Step (code counter) s₄ s₅ := by
    cases b <;> simp [Step, successors, next, code, s₀, s₁, s₂, s₃, s₄, s₅,
      start, Instruction.next, Configuration.updateTape, Configuration.advance]
  have r₆ : Step (code counter) s₅ s₆ := by
    cases b <;> simp [Step, successors, next, code, s₀, s₁, s₂, s₃, s₄, s₅, s₆,
      start, Instruction.next]
  have r₇ : Step (code counter) s₆ s₇ := by
    simp [Step, successors, next, code, s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇,
      start, Instruction.next, Configuration.updateTape, Configuration.advance]
  have r₈ : Step (code counter) s₇ s₈ := by
    cases p <;> simp [Step, successors, next, code, s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈,
      start, Tape.ofBits, Tape.moveRight, Instruction.next, Configuration.tape]
  have r₉ : Step (code counter) s₈ s₉ := by
    simp [Step, successors, next, code, s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉,
      start, Instruction.next, Configuration.updateTape, Configuration.advance]
  have r₁₀ : Step (code counter) s₉
      (start (some p::some b::some a::before)
        (some (if counter then true else b)::written) rest) := by
    cases rest <;> simp [Step, successors, next, code, s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉,
      start, Tape.ofBits, Tape.moveRight, Tape.write, Instruction.next]
  exact ((((((((((RunsFor.zero _).succ r₁).succ r₂).succ r₃).succ r₄).succ r₅).succ r₆).succ r₇).succ r₈).succ r₉).succ r₁₀

private theorem end_runs (counter : Bool) (before written : List (Option Bool)) :
    RunsFor (code counter) (start before written []) (finish before written) 2 := by
  let s₀ := start before written []
  let s₁ := { s₀ with pc := 13 }
  have r₁ : Step (code counter) s₀ s₁ := by
    simp [Step, successors, next, code, start, s₀, s₁, Instruction.next, Configuration.tape, Tape.ofBits]
  have r₂ : Step (code counter) s₁ (finish before written) := by
    simp [Step, successors, next, code, start, finish, s₀, s₁, Instruction.next, Tape.ofBits]
  exact ((RunsFor.zero _).succ r₁).succ r₂

private theorem runs_context (counter : Bool) (columns : List BinaryModularAddition.Column)
    (before written : List (Option Bool)) :
    RunsFor (code counter) (start before written (BinaryModularAddition.interleave columns))
      (finish ((BinaryModularAddition.interleave columns).reverse.map some ++ before)
        ((selected counter columns).reverse.map some ++ written)) (10*columns.length+2) := by
  induction columns generalizing before written with
  | nil => simpa [BinaryModularAddition.interleave, selected] using end_runs counter before written
  | cons column rest ih =>
    rcases column with ⟨⟨a,b⟩,p⟩
    have r := column_runs counter a b p (BinaryModularAddition.interleave rest) before written
    have result := r.trans (ih (some p::some b::some a::before)
      (some (if counter then true else b)::written))
    simpa [start, finish, selected, BinaryModularAddition.interleave,
      List.reverse_append, List.map_append, List.append_assoc,
      Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

/-- The projected q field is copied from real middle cells, with an arbitrary
saved input prefix and previous output block retained in the layout. -/
theorem runs_middle (columns : List BinaryModularAddition.Column)
    (before written : List (Option Bool)) :
    RunsFor program
      ({ inputTape := { Tape.ofBits (BinaryModularAddition.interleave columns) with left := before }
         outputTape := { left := written } } : Configuration)
      ({ pc := 13
         halted := true
         inputTape := { left := (BinaryModularAddition.interleave columns).reverse.map some ++ before }
         outputTape := { left := (columns.map (fun column => column.1.2)).reverse.map some ++ written } } : Configuration)
      (10*columns.length+2) := by
  simpa only [program, start, finish, selected, Bool.false_eq_true, ↓reduceIte] using
    runs_context false columns before written

/-- One width-counter cell is generated per actual complete three-cell row. -/
theorem runs_counter (columns : List BinaryModularAddition.Column)
    (before written : List (Option Bool)) :
    RunsFor counterProgram
      ({ inputTape := { Tape.ofBits (BinaryModularAddition.interleave columns) with left := before }
         outputTape := { left := written } } : Configuration)
      ({ pc := 13
         halted := true
         inputTape := { left := (BinaryModularAddition.interleave columns).reverse.map some ++ before }
         outputTape := { left := List.replicate columns.length (some true) ++ written } } : Configuration)
      (10*columns.length+2) := by
  simpa [counterProgram, start, finish, selected, List.map_const] using
    runs_context true columns before written

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program := by simp [program, code]
theorem counter_no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ counterProgram := by simp [counterProgram, code]

end Machine.SecondColumnGather
