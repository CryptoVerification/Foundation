import Foundation.Quantum.QKD.BB84KeyVerification
import Foundation.Quantum.QKD.ReconciliationVerification
import Foundation.Quantum.QKD.CommonKeyExamples
import Foundation.Quantum.QKD.CollisionExamples
import Foundation.Quantum.QKD.PairwiseAttackExamples

/-! An exact residual-error example, and an explicit numerical budget on the
existing real joint BB84 attack. These are correctness checks, not secrecy or
authentication claims for the additionally disclosed verification tag. -/
namespace Foundation.Quantum.QKD.KeyVerificationExamples
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false

def checked := KeyVerification.accepted CommonKeyExamples.state
  CollisionExamples.seeds CollisionExamples.hash

def rejected := KeyVerification.aborted CommonKeyExamples.state
  CollisionExamples.seeds CollisionExamples.hash

/-- Input mismatch weight 1/4 is halved by the one-bit verification family. -/
theorem residual_error : CommonKey.correctnessError checked = 1/8 := by
  rw [checked, KeyVerification.correctness_expansion]
  norm_num [CommonKeyExamples.state, ofCQ, CommonKeyExamples.cq,
    Fintype.sum_prod_type, Fin.sum_univ_two, Collision.collision, eventProb_toReal,
    CollisionExamples.seed_weight, CollisionExamples.hash, Matrix.trace_smul,
    CommonKeyExamples.reference.normalized]

theorem passing_mass : mass checked = 7/8 := by
  rw [checked, KeyVerification.accepted, mass_relabel, mass_restrict]
  norm_num [seed, CommonKeyExamples.state, ofCQ, CommonKeyExamples.cq,
    KeyVerification.passes, Fintype.sum_prod_type, Fin.sum_univ_two,
    CollisionExamples.seed_weight, CollisionExamples.hash, Matrix.trace_smul,
    CommonKeyExamples.reference.normalized]

theorem rejection_mass : mass rejected = 1/8 := by
  have h := KeyVerification.branch_mass CommonKeyExamples.state
    CollisionExamples.seeds CollisionExamples.hash
  change mass checked + mass rejected = _ at h
  rw [passing_mass, CommonKeyExamples.state, mass_ofCQ] at h
  linarith

/-- A failed key agreement is genuinely possible; verification is not a rule
that assumes correctness, nor does it force acceptance to zero. -/
theorem sharp : CommonKey.correctnessError checked =
    (1/2:ℝ) * CommonKey.correctnessError CommonKeyExamples.state := by
  rw [residual_error, CommonKeyExamples.correctness]
  norm_num

/-- Coherence is retained even on a wrong-key branch that passes the test. -/
theorem retained_wrong_key_coherence :
    checked.block ((0,1),((1,0),0)) 0 1 = 1/32 := by
  norm_num [checked, KeyVerification.accepted, relabel, restrict, seed,
    KeyVerification.acceptLabel, KeyVerification.transcript, KeyVerification.passes,
    CommonKeyExamples.state, ofCQ, CommonKeyExamples.cq,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.sum_apply, Matrix.smul_apply,
    CollisionExamples.seed_weight, CollisionExamples.hash, CommonKeyExamples.reference,
    PrivacyAmplificationExamples.reference, prepare_plus_matrix]

/-- Eight fresh public verification bits on the same two-signal coherent
joint attack bound the *unconditional accepted* mismatch weight by 1/256.
This does not say that a one-bit secret key survives disclosing eight tags. -/
theorem attacked_raw_verification :
    CommonKey.correctnessError
      (BB84KeyVerification.accepted (tag := 8) PairwiseAttackExamples.attack 1 1 0) ≤ 1/256 := by
  have h := BB84KeyVerification.correctness (tag := 8) PairwiseAttackExamples.attack 1 1 0
  convert h using 1
  norm_num [IdealKey.Key, Fintype.card_fun, Fintype.card_fin]

end
end Foundation.Quantum.QKD.KeyVerificationExamples
