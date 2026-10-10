import Foundation.Quantum.QKD.PairwiseRawHashPrivacy
import Foundation.Quantum.QKD.PublicRegisterClassical
import Foundation.Quantum.QKD.PublicKeyProcess

/-! The same accepted hashed approximant with the test values, fresh hash
seed, and detailed error record explicitly public. Its comparator uses its
own public-and-quantum marginal, not an independent postulated state. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false

def testedSource {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration n) :=
  relabel (acceptedAlice v hv k gap minKey tolerance c) (testEquiv c.2)

theorem testedSource_diagonal {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration n) :
    PublicRegisterExpose.Diagonal (testedSource v hv k gap minKey tolerance c) :=
  PublicRegisterExpose.relabel_diagonal _ (PublicRegisterExpose.withPublic_diagonal _) _

def publishedHash {n length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration n) :=
  PublicRegisterExpose.expose (HashLayout.output (testedSource v hv k gap minKey tolerance c)
    (Foundation.Probability.uniform (Hashing.RawSeed n length)) (remainingHash c.2))

theorem published_secrecy {n length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration n) :
    OperatorApprox (joint (publishedHash (length := length) v hv k gap minKey tolerance c))
      (joint (CommonKey.uniformize (publishedHash (length := length) v hv k gap minKey tolerance c)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) * ((1-1/Fintype.card (IdealKey.Key length))*
        (((2:ℝ)^c.2.card * bound k gap minKey tolerance c)*1)))) := by
  apply PublicRegisterExpose.secrecy
    (HashLayout.output (testedSource v hv k gap minKey tolerance c) _ (remainingHash c.2))
    (PublicRegisterExpose.hash_output_diagonal _ (testedSource_diagonal _ _ _ _ _ _ _) _ _) _
  apply HashLayout.secrecy
  exact rawHashPrivacy v hv k gap minKey tolerance c

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
