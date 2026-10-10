import Foundation.Quantum.QKD.PairwiseVerificationRaw
import Foundation.Quantum.QKD.PublicRegisterSeeded

/-! Explicit classical public labels for the same checked support-state hash
experiment. Exposing registers reorders their classical slices and keeps every
quantum auxiliary entry. The private-key comparator is transformed identically. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized PureProjection
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

def verifiedDisclosure {n tag : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) (s : Hashing.RawSeed n tag) :=
  disclose (verifiedSource v hv k gap minKey tolerance c s) (fun x _ => remainingHash c.2 s x)

theorem verifiedDisclosure_diagonal {n tag : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) (s : Hashing.RawSeed n tag) :
    PublicRegisterExpose.Diagonal (verifiedDisclosure v hv k gap minKey tolerance c s) := by
  unfold verifiedDisclosure disclose verifiedSource
  rw [verifiedAlice_coordinates]
  exact PublicRegisterExpose.relabel_diagonal _
    (PublicRegisterExpose.relabel_diagonal _ (PublicRegisterExpose.withPublic_diagonal _) _) _

def verifiedTestExposed {n tag length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) (s : Hashing.RawSeed n tag) :=
  PublicRegisterExpose.expose (HashLayout.output
    (withPublic (verifiedDisclosure v hv k gap minKey tolerance c s))
    (Foundation.Probability.uniform (Hashing.RawSeed n length)) (remainingHash c.2))

theorem verifiedTestExposed_eq {n tag length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) (s : Hashing.RawSeed n tag) :
    verifiedTestExposed (length := length) v hv k gap minKey tolerance c s =
      relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (verifiedDisclosure v hv k gap minKey tolerance c s))
        (fun rx => (remainingHash c.2 rx.1 rx.2.1.1,((rx.2.1.2,rx.1),rx.2.2))) :=
  PublicRegisterExpose.expose_seed_relabel _ _ _

theorem verifiedTestExposed_diagonal {n tag length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) (s : Hashing.RawSeed n tag) :
    PublicRegisterExpose.Diagonal (verifiedTestExposed (length := length) v hv k gap minKey tolerance c s) := by
  rw [verifiedTestExposed_eq]
  exact PublicRegisterExpose.relabel_diagonal _
    (PublicRegisterExpose.seed_diagonal _ _ (verifiedDisclosure_diagonal _ _ _ _ _ _ _ _)) _

def verifiedPublished {n tag length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) (s : Hashing.RawSeed n tag) :=
  PublicRegisterExpose.expose (verifiedTestExposed (length := length) v hv k gap minKey tolerance c s)

theorem verified_published_secrecy {n tag length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) (s : Hashing.RawSeed n tag) :
    OperatorApprox (joint (verifiedPublished (length := length) v hv k gap minKey tolerance c s))
      (joint (CommonKey.uniformize (verifiedPublished (length := length) v hv k gap minKey tolerance c s)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) *
        ((1-1/Fintype.card (IdealKey.Key length))*
          ((Fintype.card (IdealKey.Key tag)*((2:ℝ)^c.2.card * bound k gap minKey tolerance c))*1)))) := by
  apply PublicRegisterExpose.secrecy _ (verifiedTestExposed_diagonal _ _ _ _ _ _ _ _) _
  apply PublicRegisterExpose.secrecy _
    (PublicRegisterExpose.hash_output_diagonal _ (PublicRegisterExpose.withPublic_diagonal _) _ _) _
  apply HashLayout.secrecy
  exact verified_hash_privacy v hv k gap minKey tolerance c s

/-- Both exposed registers and the PA seed are the specified deterministic
processing of the same checked measurement coordinates. -/
theorem verifiedPublished_eq {n tag length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) (s : Hashing.RawSeed n tag) :
    verifiedPublished (length := length) v hv k gap minKey tolerance c s =
      relabel (seed (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (checkedCoordinates v hv k gap minKey tolerance c s))
        (fun rx => (remainingHash c.2 rx.1 (testEquiv c.2 rx.2.1).1,
          (((remainingHash c.2 s (testEquiv c.2 rx.2.1).1,rx.1),
            (testEquiv c.2 rx.2.1).2),rx.2.2))) := by
  unfold verifiedPublished
  rw [verifiedTestExposed_eq]
  unfold verifiedDisclosure disclose verifiedSource
  rw [verifiedAlice_coordinates, seed_relabel, seed_relabel, relabel_comp, relabel_comp]
  exact PublicRegisterExpose.expose_seed_relabel _ _ _

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
