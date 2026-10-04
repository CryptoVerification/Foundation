import Foundation.Machine.BinaryHighZeroTrim

namespace Foundation.Examples.ScalarWidth

/-- A native postprocessing trace keeps the drawn low bits and writes the
remaining high zeros. The result matches the scalar's fixed-width encoding. -/
example : ∃ target used, used ≤ 33 ∧
    Machine.RunsFor Machine.FixedWidthOutputPadding.program
      ({ inputTape := Machine.Tape.ofBits (List.replicate 6 true),
         outputTape := Machine.Tape.ofBits [true, false] } : Machine.Configuration)
      target used ∧ target.halted = true ∧
      target.outputBits = Machine.Binary.encode 6 1 := by
  obtain ⟨target, used, hUsed, run, hHalt, hBits⟩ :=
    Machine.FixedWidthOutputPadding.runs 6 [true, false] (by decide)
  exact ⟨target, used, hUsed, run, hHalt, by simpa [Machine.Binary.encode] using hBits⟩

/-- Remove only the high padding from q=3; this is the canonical raw input
required by the existing exact sampler, rather than sampling all six bits. -/
example (input : Machine.Tape) :
    Machine.RunsFor Machine.BinaryHighZeroTrim.program
      ({ inputTape := input,
         outputTape := { left := (Machine.Binary.encode 6 3).reverse.map some } } : Machine.Configuration)
      ({ pc := 6, halted := true, inputTape := input,
         outputTape := { left := (Nat.bits 3).reverse.map some,
                         right := List.replicate (6-(Nat.bits 3).length) none } } : Machine.Configuration)
      (4*(6-(Nat.bits 3).length)+4) :=
  Machine.BinaryHighZeroTrim.runs_number input 6 3 (by decide) (by decide)

end Foundation.Examples.ScalarWidth
