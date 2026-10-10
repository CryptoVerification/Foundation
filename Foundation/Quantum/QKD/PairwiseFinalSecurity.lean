import Foundation.Quantum.QKD.FinalAcceptedHash
import Foundation.Quantum.QKD.PairwiseRealSecrecy

/-! Connect the proved actual Alice secrecy to the existing full finalization
ideal, including unchanged abort branches. Actual key disagreement remains an
explicit correctness cost; no error correction or authentication is assumed. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false

theorem final_security_of_correctness {n length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) (δ : ℝ)
    (hc : CommonKey.correctnessError (FinalSecurity.acceptedBranch A k minKey tolerance
      (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash) ≤ δ) :
    IdealKey.Secure (Hashing.linearState (length := length) A k minKey tolerance)
      (δ + (2*PairwiseRandomizedSampling.error n k gap + privacyError n length k gap minKey tolerance)) := by
  apply FinalSecurity.secure _ _ _ _ _ _ _ _ hc
  have hs := real_accepted_secrecy (length := length) A k gap minKey tolerance
  unfold realAcceptedHash at hs
  rw [FinalSecurity.alice_accepted_hash] at hs
  exact hs

def finalCorrectnessCost {n length : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) : ℝ :=
  CommonKey.correctnessError (FinalSecurity.acceptedBranch A k minKey tolerance
    (Foundation.Probability.uniform (Hashing.RawSeed n length)) Hashing.rawHash)

theorem final_correctness_probability {n length : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) :
    (recordEvent e (fun r => let o : IdealKey.Output (Finalization.Transcript n (Hashing.RawSeed n length)) length :=
      (Fintype.equivFin _).symm r; o.aliceKey ≠ o.bobKey)).probability
        (Hashing.linearState (length := length) A k minKey tolerance) =
      finalCorrectnessCost (length := length) A k minKey tolerance :=
  FinalSecurity.correctness_probability _ _ _ _ _ _

theorem final_security_with_actual_cost {n length : Nat} {e : Space} (A : BlockAttack n e)
    (k gap minKey tolerance : Nat) :
    IdealKey.Secure (Hashing.linearState (length := length) A k minKey tolerance)
      (finalCorrectnessCost (length := length) A k minKey tolerance +
        (2*PairwiseRandomizedSampling.error n k gap + privacyError n length k gap minKey tolerance)) :=
  final_security_of_correctness A k gap minKey tolerance _ le_rfl

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
