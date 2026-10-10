import Foundation.Quantum.QKD.UniformFiber
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! A concrete two-universal family: uniformly random binary matrices.
The exact collision probability for distinct inputs is 2^(-output length).
This is the combinatorial premise of privacy amplification, not the quantum
leftover-hash theorem. -/
namespace Foundation.Quantum.QKD.Hashing
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I O : Type} [Fintype I]

abbrev Bits (I : Type) := I → ZMod 2
abbrev Seed (I O : Type) := Matrix O I (ZMod 2)

def linearHash (M : Seed I O) (x : Bits I) : Bits O := M.mulVec x

/-- A nonzero input difference permits any output difference; a single
 nonzero column suffices to construct a preimage. -/
theorem hash_difference_surjective (d : Bits I) (hd : d ≠ 0) :
    Function.Surjective (Matrix.mulVec.addMonoidHomLeft (m := O) d) := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hd (funext hn)
  intro y
  refine ⟨fun o i => if i = j then y o / d j else 0, ?_⟩
  funext o
  change (∑ i, (if i = j then y o / d j else 0) * d i) = y o
  simp [ite_mul]
  exact div_mul_cancel₀ _ hj

variable [Fintype O] [DecidableEq I] [DecidableEq O]

/-- Exact two-universality, valid for every pair of different binary inputs
 and any finite output index set, including the empty output. -/
theorem linear_collision (x y : Bits I) (hxy : x ≠ y) :
    (Foundation.Probability.eventProb (Foundation.Probability.uniform (Seed I O))
      (fun M => linearHash M x = linearHash M y)).toReal = 1 / (2 : ℝ) ^ Fintype.card O := by
  have hd : x-y ≠ 0 := sub_ne_zero.mpr hxy
  have heq : (fun M : Seed I O => linearHash M x = linearHash M y) =
      (fun M => (Matrix.mulVec.addMonoidHomLeft (m := O) (x-y)) M = 0) := by
    funext M
    apply propext
    change M.mulVec x = M.mulVec y ↔ M.mulVec (x-y) = 0
    rw [Matrix.mulVec_sub, sub_eq_zero]
  rw [heq, uniform_hom_fiber _ (hash_difference_surjective (O := O) _ hd)]
  simp [ZMod.card]

end
end Foundation.Quantum.QKD.Hashing
