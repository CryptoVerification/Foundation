import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Init
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp

namespace Secrecy

open scoped BigOperators

lemma sum_mul_right_finset {β : Type _} (s : Finset β) (f : β → ℚ) (c : ℚ) :
    (∑ b ∈ s, f b * c) = (∑ b ∈ s, f b) * c := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha hInd
    simp [Finset.sum_insert, ha, hInd, right_distrib]

lemma sum_mul_right {β : Type _} [Fintype β] [DecidableEq β]
    (f : β → ℚ) (c : ℚ) :
    (∑ b : β, f b * c) = (∑ b : β, f b) * c := by
  classical
  simpa using
    (sum_mul_right_finset (s := (Finset.univ : Finset β)) f c)

lemma sum_natCast {α : Type _} [Fintype α] (f : α → ℕ) :
    (∑ a, (f a : ℚ)) = ((∑ a, f a : ℕ) : ℚ) := by
  classical
  let s : Finset α := Finset.univ
  have hCast :
      s.sum (fun a => (f a : ℚ)) =
        ((s.sum (fun a => f a) : ℕ) : ℚ) := by
    refine Finset.induction_on s ?base ?step
    · simp
    · intro a t ha hInd
      simp [ha, hInd]
  simpa using hCast

end Secrecy
