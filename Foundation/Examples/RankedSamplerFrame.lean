import Foundation.Crypto.Semantics.Machine.RankedFamilyRefinement
import Foundation.Crypto.Semantics.Machine.TapeObservationAssertions
import Foundation.Crypto.Semantics.Machine.PrivateBitGenerationRanking

/-! Combine independently proved sampling termination and input-bit
preservation at every finite input, including empty and non-marker inputs.
There is one runtime code. Refinement adds neither time nor physical state. -/
namespace Foundation.Examples.RankedSamplerFrame
open Machine Foundation.Probability TimedExecution
open Machine.PrivateBitGeneration
set_option backward.isDefEq.respectTransparency false

noncomputable def base : Program.RankedFamily OneTimePad.keygen (List Bool) where
  assertions := fun _ => Ranked.assertions
  verified := fun _ => Ranked.verified
  ranking := fun _ => Ranked.ranking
  entry := Configuration.initial
  valid := Ranked.initial_valid

def extra (bits : List Bool) : Program.Assertions :=
  TapeObservationAssertions.assertions .input bits

theorem extra_verified (bits : List Bool) : (extra bits).Verified OneTimePad.keygen :=
  TapeObservationAssertions.verified _ _ (by decide) bits

theorem extra_initial (bits : List Bool) : (extra bits).Holds (base.entry bits) := by
  apply (TapeObservationAssertions.holds .input bits _).mpr
  exact Tape.bits_ofBits bits

noncomputable def refined := base.enrich extra extra_verified extra_initial

theorem budget (bits : List Bool) : refined.execution.budget bits = 5 * bits.length + 2 := by
  dsimp only [refined]
  rw [Program.RankedFamily.enrich_budget, Program.RankedFamily.budget]
  change Ranked.rank (Configuration.initial bits) + 1 = _
  simp [Ranked.rank, Configuration.initial, Ranked.remaining_initial]

theorem same_costed (bits : List Bool) : refined.execution.costed bits = base.execution.costed bits :=
  base.enrich_costed extra extra_verified extra_initial bits

/-- Clients of the old contract receive the stronger conclusion too. -/
theorem input_bits (bits : List Bool) (target : Configuration)
    (hTarget : target ∈ (base.execution.semantics bits).support) : target.inputTape.bits = bits :=
  base.extra_postcondition extra extra_verified extra_initial bits target hTarget

def spaceProfile : Nat → Nat :=
  Program.RankedFamily.profile (code := OneTimePad.keygen)
    (fun _ => 0) (fun width => width + 2) (fun width => 5 * width + 2)

theorem space_polynomial : PolynomiallyBounded spaceProfile :=
  Program.RankedFamily.profile_polynomial (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2))
    (((PolynomiallyBounded.const 5).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 2))

/-- One common bound covers all bitstrings of the given length. -/
theorem storage_peak (bits : List Bool) (elapsed : Nat) (hElapsed : elapsed ≤ 5 * bits.length + 2)
    (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF OneTimePad.keygen) elapsed
      (Configuration.initial bits)).support) :
    (NativeEncodedResources.completeEncoding.encode (OneTimePad.keygen, target)).length ≤
      spaceProfile bits.length := by
  apply base.storage_profile (fun _ => 0) (fun width => width + 2) (fun width => 5 * width + 2)
    (fun width input => input.length = width) _ _ _ bits.length bits rfl elapsed _ target hTarget
  · intro width input _
    exact Nat.le_refl 0
  · intro width input hLength
    have h := Tape.cells_ofBits_le input
    change (Tape.ofBits input).cells + 1 ≤ width + 2
    omega
  · intro width input hLength
    change Ranked.rank (Configuration.initial input) + 1 ≤ _
    simp [Ranked.rank, Configuration.initial, Ranked.remaining_initial, hLength]
  · change elapsed ≤ Ranked.rank (Configuration.initial bits) + 1
    simpa [Ranked.rank, Configuration.initial, Ranked.remaining_initial, Nat.add_assoc] using hElapsed

/-- A destructive input write cannot obtain this syntactic certificate. -/
theorem input_write_rejected : ¬ Program.preservesBits [Instruction.write .input false] .input := by
  decide

end Foundation.Examples.RankedSamplerFrame
