import Foundation.Crypto.Semantics.Machine.SavedFramedScalarSampler
import Foundation.Crypto.Semantics.Machine.SavedRejectionSamplingSemantics
import Foundation.Crypto.Semantics.Machine.OverwriteInputField

namespace Foundation.Examples.SavedFramedScalarSampler

open Machine

/-- A real accepted scalar-1 branch retains the entire p=7,q=3,g=2 request
under its width counter, so later arithmetic can recover its public fields. -/
example :
    let raw := encodeSecurityParameter 3 ++
      frame (Binary.encode 6 7 ++ Binary.encode 6 3 ++ Binary.encode 6 2)
    ∃ target used, used ≤ Machine.SavedFramedScalarInput.validBudget 3
        (Binary.encode 6 7) (Binary.encode 6 2) + 142 ∧
      RunsFor Machine.SavedFramedScalarSampler.program (Configuration.initial raw) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent {left := List.replicate 6 (some true) ++ none::raw.reverse.map some} ∧
      target.outputBits = Binary.encode 6 1 := by
  dsimp only
  let raw := encodeSecurityParameter 3 ++
    frame (Binary.encode 6 7 ++ Binary.encode 6 3 ++ Binary.encode 6 2)
  let before := List.replicate 6 (some true) ++ none::raw.reverse.map some
  let draw : Fin ([true]++[true]).length → Bool := fun i => decide (i.val = 0)
  obtain ⟨accepted, u, hu, sourceRun, sourceHalt, sourceInput, sourceOutput⟩ :=
    RejectionSampling.Saved.runs_first_trial before [true] (by decide) draw (by decide)
  obtain ⟨target, used, hUsed, run, halt, retained, output⟩ :=
    Machine.SavedFramedScalarSampler.runs_from_sample 3 (Binary.encode 6 7) (Binary.encode 6 2)
      3 (by simp) (by decide) (by decide) (List.ofFn draw) (by simp [draw])
      accepted u sourceRun sourceHalt sourceInput sourceOutput
  have count : u ≤ 45 := by simpa [RejectionSampling.preparationSteps] using hu
  have value : Binary.value (List.ofFn draw) = 1 := by decide
  exact ⟨target, used, by omega, run, halt, retained, value ▸ output⟩

/-- Copy the sampled scalar into the three-bit exponent field while
preserving the following generator bits and the scalar source itself. -/
example : RunsFor OverwriteInputField.program
    ({inputTape := Tape.ofBits ([true,true,false]++[false,true,false]),
      outputTape := Tape.ofBits [true,false,false]} : Configuration)
    ({pc := 8, halted := true,
      inputTape := {Tape.ofBits [false,true,false] with left := [some false,some false,some true]},
      outputTape := {left := [some false,some false,some true]}} : Configuration) 20 := by
  exact OverwriteInputField.runs [] [] [true,true,false] [false,true,false] [true,false,false] rfl

end Foundation.Examples.SavedFramedScalarSampler
