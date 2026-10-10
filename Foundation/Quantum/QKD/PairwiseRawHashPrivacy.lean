import Foundation.Quantum.QKD.PairwiseOptionalKey

/-! The existing position-labelled BB84 binary-matrix hash, applied to the
remaining actual Alice key of the same sampling approximant. Public test values,
detailed errors, fresh hash seed and all quantum auxiliaries remain present. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem rawHashPrivacy {n length : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ)
    (hv : PureProjection.bracket v v = 1) (k gap minKey tolerance : Nat)
    (c : PairwiseSampling.Configuration n) :
    OperatorApprox
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun s => Collision.hashed (testedKey v hv k gap minKey tolerance c).block (remainingHash c.2 s)))
      (publicMixture (Foundation.Probability.uniform (Hashing.RawSeed n length))
        (fun _ => Collision.uniformComparator (Y := IdealKey.Key length)
          (testedKey v hv k gap minKey tolerance c).block))
      ((1/2:ℝ)*Real.sqrt (Fintype.card (IdealKey.Key length) * ((1-1/Fintype.card (IdealKey.Key length))*
        (((2:ℝ)^c.2.card * bound k gap minKey tolerance c)*1)))) :=
  testedPrivacy v hv k gap minKey tolerance c _ (remainingHash c.2) (remaining_collision c.2)

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
