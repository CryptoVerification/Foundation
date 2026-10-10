import Foundation.Quantum.QKD.PairwiseRecoveredSupport
import Foundation.Quantum.RetainedInstrumentPost

/-! The recovered sampling approximation followed by the actual complementary
key rotation. The real side is exactly the existing original BB84 first
measurement on the original attacked selected source. -/
namespace Foundation.Quantum.QKD.PairwiseRecovery
noncomputable section
open BB84DelayedMeasurements BB84PairwiseReference PairwiseRecordedSampling BB84ErrorTransform
set_option backward.isDefEq.respectTransparency false

def keyRotation (n : Nat) (e : Space) : Channel (output n e) (output n e) :=
  RetainedControl.channel (fun t => RetainedControl.channel (fun _ : Fin (count n) =>
    (keyChannel (basis ((Fintype.equivFin (PairwiseSampling.Configuration n)).symm t))).amplify e))

theorem key_public {n : Nat} {e : Space} (p : PMF (PairwiseSampling.Configuration n))
    (ρ : Density (jointSpace n e)) :
    (keyRotation n e).toKraus.apply
      (publicMixture p (fun c => (PartitionMeasurement.instrument (errorLabel (basis c))).record.toKraus.apply
        (referenceInput ρ).matrix)) =
      publicMixture p (fun c => (actualFirst (basis c) e).record.toKraus.apply ρ.matrix) := by
  rw [keyRotation, RetainedControl.public_apply]
  apply congrArg (publicMixture p)
  funext c
  simp only [Equiv.symm_apply_apply]
  rw [Instrument.retained_post
    (PartitionMeasurement.instrument (errorLabel (basis c) (e := e)))
    ((keyChannel (basis c)).amplify e)]
  have h := actual_reference (basis c) e ρ.matrix
  rw [referenceFirst, Instrument.record_pre] at h
  change (actualFirst (basis c) e).record.toKraus.apply ρ.matrix =
    ((PartitionMeasurement.instrument (errorLabel (basis c))).post ((keyChannel (basis c)).amplify e)).record.toKraus.apply
      ((((cnotChannel n).amplify e).seq ((referenceChannel n).amplify e)).toKraus.apply ρ.matrix) at h
  rw [Channel.seq, Kraus.seq_apply] at h
  exact h.symm

def original {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :=
  (keyRotation (BB84SiftedInput.selectedCount M) (BB84SiftedInput.auxiliary M e)).run (actual A M k hk)

theorem original_eq {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :
    (original A M k hk).matrix =
      publicMixture (PairwiseSampling.distribution (BB84SiftedInput.selectedCount M) k hk)
        (fun c => ((actualFirst (basis c) (BB84SiftedInput.auxiliary M e)).record.run
          (BB84SiftedInput.input A M)).matrix) := key_public _ _

def originalApproximant {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :=
  (keyRotation (BB84SiftedInput.selectedCount M) (BB84SiftedInput.auxiliary M e)).run (approximant A M k gap hk)

/-- The full public-selector joint original first measurement and a constructed
normalized approximant satisfy the proved finite-count sampling error. -/
theorem original_approximation {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (k gap : Nat) (hk : k ≤ BB84SiftedInput.selectedCount M) :
    StateApprox (original A M k hk) (originalApproximant A M k gap hk)
      (Real.sqrt (PairwiseSampling.errorBound (BB84SiftedInput.selectedCount M) k gap).toReal) :=
  (recovered_approximation A M k gap hk).postprocess (keyRotation _ _)

end
end Foundation.Quantum.QKD.PairwiseRecovery
