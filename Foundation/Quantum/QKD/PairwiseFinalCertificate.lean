import Foundation.Quantum.QKD.PairwiseRandomizedCertificate

/-! Transfer the proved full raw sampling error to the actual full finalized
BB84 experiment, with fresh public hash randomness and both private outputs.
The comparison is the constructed sampling certificate, not an ideal secret
key resource; secrecy and correctness of that certificate remain obligations. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
set_option backward.isDefEq.respectTransparency false

def finalCertificate {n length : Nat} {e : Space} {S : Type} [Fintype S]
    (A : BlockAttack n e) (k gap minKey tolerance : Nat)
    (p : PMF S) (h : S → Finalization.RawKey n → IdealKey.Key length) :=
  Density.mixture p (fun seed =>
    (Finalization.channel e seed h).run (certificate A k gap minKey tolerance))

theorem final_certificate_approximation {n length : Nat} {e : Space} {S : Type} [Fintype S]
    (A : BlockAttack n e) (k gap minKey tolerance : Nat)
    (p : PMF S) (h : S → Finalization.RawKey n → IdealKey.Key length) :
    StateApprox (Finalization.state A k minKey tolerance p h)
      (finalCertificate A k gap minKey tolerance p h) (PairwiseRandomizedSampling.error n k gap) :=
  StateApprox.mixture_uniform_bound p _ _
    (fun seed => (certificate_approximation A k gap minKey tolerance).postprocess
      (Finalization.channel e seed h))

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
