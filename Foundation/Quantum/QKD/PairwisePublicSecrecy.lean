import Foundation.Quantum.QKD.PairwisePublicTranscript

/-! Accepted Alice-key secrecy with the actual public raw transcript and
fresh hash seed. The comparator preserves this same state's public/quantum
marginal and its acceptance mass. Whole-protocol restoration is separate. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
set_option backward.isDefEq.respectTransparency false

def publishedRawHash {n length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration n) :=
  CommonKey.publicProcess (publishedHash (length := length) v hv k gap minKey tolerance c)
    (fun p => (testTranscript c p.1.1 p.2,p.1.2))

theorem public_raw_secrecy {n length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration n) :
    OperatorApprox (Subnormalized.joint (publishedRawHash (length := length) v hv k gap minKey tolerance c))
      (Subnormalized.joint (CommonKey.uniformize (publishedRawHash (length := length) v hv k gap minKey tolerance c)))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) * ((1-1/Fintype.card (IdealKey.Key length))*
        (((2:ℝ)^c.2.card * bound k gap minKey tolerance c)*1)))) :=
  CommonKey.publicProcess_secrecy _ _ _ (published_secrecy v hv k gap minKey tolerance c)

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
