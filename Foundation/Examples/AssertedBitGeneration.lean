import Foundation.Crypto.Semantics.Machine.AssertedProcedure
import Foundation.Crypto.Semantics.Machine.PrivateBitGeneration
import Foundation.Crypto.Semantics.Machine.TapeObservationAssertions

/-! Derive an input-dependent typed contract for the actual arbitrary-width
native sampler using local instruction assertions. All prefixes preserve the
marker bit sequence; physical head motion is still present and charged. -/
namespace Foundation.Examples.AssertedBitGeneration
open Machine Foundation.Probability TimedExecution

def assertions (markers : List Bool) : Machine.Program.Assertions where
  active _ input _ := input.bits = markers
  stopped _ input _ := input.bits = markers

theorem verified (markers : List Bool) : (assertions markers).Verified OneTimePad.keygen := by
  exact TapeObservationAssertions.verified OneTimePad.keygen .input (by decide) markers

theorem initial_valid (width : Nat) (input : Unit) :
    (assertions (List.replicate width true)).Holds
      ((PrivateBitGeneration.native width).execution.entry input) := by
  change (Tape.ofBits (List.replicate width true)).bits = List.replicate width true
  exact Tape.bits_ofBits _

theorem operational (width : Nat) :
    TimedExecution.Procedure.Operational (PrivateBitGeneration.native width).execution := by
  dsimp only [PrivateBitGeneration.native, Machine.Procedure.ofFixed]
  apply TimedExecution.Procedure.operational_ofFixed

/-- A typed endpoint derived from the verified local assertions, with all
physical state and the original actual cost distribution retained. -/
noncomputable def native (width : Nat) :=
  Machine.AssertedProcedure.native (PrivateBitGeneration.native width)
    (fun _ => assertions (List.replicate width true)) (fun _ => verified _)
    (initial_valid width) (operational width)

theorem code (width : Nat) : (native width).code = OneTimePad.keygen := rfl

theorem budget (width : Nat) : (native width).execution.budget () = 5 * width + 2 := rfl

/-- The condition holds throughout the sampler, including after its halt. -/
theorem sampler_prefix (width elapsed : Nat) (target : Configuration)
    (hTarget : target ∈ (evalConfigWithin OneTimePad.keygen
      (Configuration.initial (List.replicate width true)) elapsed).support) :
    target.inputTape.bits = List.replicate width true := by
  have h := (verified (List.replicate width true)).prefix _ _ (initial_valid width ()) elapsed hTarget
  cases hh : target.halted <;>
    simpa only [Program.Assertions.Holds, hh, Bool.false_eq_true, ↓reduceIte, assertions] using h

end Foundation.Examples.AssertedBitGeneration
