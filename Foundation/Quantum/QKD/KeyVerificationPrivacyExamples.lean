import Foundation.Quantum.QKD.KeyVerificationSeeded
import Foundation.Quantum.QKD.KeyVerificationExamples

/-! A proved domination certificate on the same nontrivial wrong-key input;
then two independent public seeds and actual tag selection before PA. -/
namespace Foundation.Quantum.QKD.KeyVerificationPrivacyExamples
noncomputable section
open Subnormalized
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

def publicCQ := Guessing.withPublic
  (Guessing.relabel CommonKeyExamples.cq (fun x => (x.1.1,x.2)))

def reference := Guessing.marginal publicCQ

theorem equal_blocks (a b : Fin 2) : publicCQ.block a = publicCQ.block b := by
  change (withPublic (CommonKey.aliceView CommonKeyExamples.state)).block a =
    (withPublic (CommonKey.aliceView CommonKeyExamples.state)).block b
  simp only [withPublic]
  simp_rw [CommonKeyExamples.alice_block]

theorem dominated : Dominated
    (withPublic (CommonKey.aliceView CommonKeyExamples.state)) reference (1/2) := by
  intro a
  have he : (1/2:ℂ) • reference.matrix = publicCQ.block a := by
    simp only [reference, Guessing.marginal, Fin.sum_univ_two]
    rw [equal_blocks 0 a, equal_blocks 1 a]
    module
  have hcast : (((1/2:ℝ):ℂ)) = (1/2:ℂ) := by norm_num
  rw [hcast]
  change ((1/2:ℂ) • reference.matrix - publicCQ.block a).PosSemidef
  rw [he, sub_self]
  exact Matrix.PosSemidef.zero

/-- One verification bit changes the domination coefficient from 1/2 to 1,
with the passing-event selection and both public registers retained. -/
theorem checked_dominated (s : Fin 2) : Dominated
    (KeyVerification.fixedInput CommonKeyExamples.state CollisionExamples.hash s)
    (leakedReference (C := Fin 2) reference) 1 := by
  have h := KeyVerification.fixed_dominated CommonKeyExamples.state CollisionExamples.hash s
    reference (1/2) dominated
  norm_num only [Fintype.card_fin, Nat.cast_ofNat, mul_one_div, div_self (by norm_num : (2:ℝ) ≠ 0)] at h
  exact h

/-- The verification seed and the independent PA seed are both explicit;
no small-secret-key claim is made from this conservative error bound. -/
theorem interpreted : OperatorApprox
    (publicMixture CollisionExamples.seeds (fun s => publicMixture CollisionExamples.seeds
      (fun r => Collision.hashed
        (KeyVerification.fixedInput CommonKeyExamples.state CollisionExamples.hash s).block
        (CollisionExamples.hash r))))
    (publicMixture CollisionExamples.seeds (fun s => publicMixture CollisionExamples.seeds
      (fun _ => Collision.uniformComparator (Y := Fin 2)
        (KeyVerification.fixedInput CommonKeyExamples.state CollisionExamples.hash s).block))) (1/2) := by
  have h := KeyVerification.averaged_privacy CommonKeyExamples.state CollisionExamples.hash
    CollisionExamples.seeds reference (1/2) (by norm_num) dominated
    CollisionExamples.seeds CollisionExamples.hash
    (fun a b hab => by
      simpa only [Fintype.card_fin, Nat.cast_ofNat] using
        le_of_eq (CollisionExamples.hash_collision a b hab))
  norm_num at h
  exact h

end
end Foundation.Quantum.QKD.KeyVerificationPrivacyExamples
