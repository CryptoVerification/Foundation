import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Init
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp

namespace Secrecy

open scoped BigOperators

variable {Key Msg Ciph : Type _}

/-- Simple rational-valued distribution on a finite type. -/
structure FiniteDistribution (α : Type _) [Fintype α] where
  prob : α → ℚ
  nonneg : ∀ a, 0 ≤ prob a
  sum_one : ∑ a, prob a = 1

namespace FiniteDistribution

variable {α : Type _} [Fintype α]

section
variable [DecidableEq α]

/-- Dirac distribution supported at `a₀`. -/
def dirac (a₀ : α) : FiniteDistribution α :=
  { prob := fun a => if a = a₀ then 1 else 0
    , nonneg := by
        intro a
        split_ifs <;> norm_num
    , sum_one := by
        classical
        have :
            ((Finset.univ : Finset α).sum fun a =>
                if a = a₀ then (1 : ℚ) else 0) = 1 := by
          simp [Finset.mem_univ]
        exact this }

@[simp]
lemma dirac_prSob (a₀ a : α) :
    (dirac (α := α) a₀).prob a = if a = a₀ then 1 else 0 := rfl

end

end FiniteDistribution

end Secrecy
