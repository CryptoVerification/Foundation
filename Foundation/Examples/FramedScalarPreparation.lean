import Foundation.Machine.FramedScalarPreparation

namespace Foundation.Examples.FramedScalarPreparation

open Machine

/-- The q=3 example has a six-cell public field, but the native sampler
preparation retains only the two canonical q bits. Six counter cells survive
below the blank separator, and the other tape is physically cleared. -/
example : ∃ (target : Configuration) (used : Nat),
    used ≤ FramedScalarPreparation.validBudget 3 (Binary.encode 6 7) (Binary.encode 6 2) ∧
    RunsFor FramedScalarPreparation.program
      (Configuration.initial (encodeSecurityParameter 3 ++
        frame (Binary.encode 6 7 ++ Binary.encode 6 3 ++ Binary.encode 6 2))) target used ∧
    target.halted = true ∧
    target.inputTape.Equivalent
      { left := [some true, some true, none] ++ List.replicate 6 (some true)
        right := List.replicate 4 none } ∧
    target.outputTape.Equivalent ({} : Tape) := by
  simpa [show Nat.bits 3 = [true, true] from rfl] using Machine.FramedScalarPreparation.runs_valid
    3 (Binary.encode 6 7) (Binary.encode 6 2) 3 (by simp) (by decide) (by decide)

/-- Preparation costs remain polynomial even for profiles whose numeric
values vary independently; their representations here all have width n+3. -/
example (modulus generator : Nat → Nat) :
    PolynomiallyBounded (fun n => Machine.FramedScalarPreparation.validBudget n
      (Binary.encode (n+3) (modulus n)) (Binary.encode (n+3) (generator n))) :=
  Machine.FramedScalarPreparation.validBudget_fixedWidth_polynomiallyBounded modulus generator

end Foundation.Examples.FramedScalarPreparation
