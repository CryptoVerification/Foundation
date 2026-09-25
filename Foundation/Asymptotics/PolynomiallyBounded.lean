import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

/-- A natural-valued profile has an eventual monomial upper bound. This says
nothing about an algorithm or a computational model, and does not require the
profile itself to be monotone. -/
def PolynomiallyBounded (r : Nat → Nat) : Prop :=
  ∃ c k : Nat, ∀ᶠ n in atTop, r n ≤ c * (n + 1) ^ k

namespace PolynomiallyBounded

theorem zero : PolynomiallyBounded (fun _ => 0) := by
  refine ⟨0, 0, Filter.Eventually.of_forall (fun n => ?_)⟩
  exact Nat.zero_le _

theorem const (c : Nat) : PolynomiallyBounded (fun _ => c) := by
  refine ⟨c, 0, Filter.Eventually.of_forall (fun n => ?_)⟩
  simp

theorem id : PolynomiallyBounded (fun n => n) := by
  refine ⟨1, 1, Filter.Eventually.of_forall (fun n => ?_)⟩
  simp

/-- An eventual upper comparison suffices; a finite prefix is irrelevant. -/
theorem mono_eventually {r s : Nat → Nat}
    (hrs : ∀ᶠ n in atTop, r n ≤ s n)
    (hs : PolynomiallyBounded s) : PolynomiallyBounded r := by
  obtain ⟨c, k, hs⟩ := hs
  refine ⟨c, k, ?_⟩
  filter_upwards [hrs, hs] with n hrn hsn
  exact hrn.trans hsn

theorem mono {r s : Nat → Nat}
    (hrs : ∀ n, r n ≤ s n)
    (hs : PolynomiallyBounded s) : PolynomiallyBounded r :=
  mono_eventually (Filter.Eventually.of_forall hrs) hs

/-- Profiles that agree eventually have the same polynomial boundedness. -/
theorem congr {r s : Nat → Nat}
    (h : r =ᶠ[atTop] s) :
    PolynomiallyBounded r ↔ PolynomiallyBounded s := by
  constructor
  · intro hr
    exact mono_eventually (h.mono (fun _ heq => le_of_eq heq.symm)) hr
  · intro hs
    exact mono_eventually (h.mono (fun _ heq => le_of_eq heq)) hs

theorem add {r s : Nat → Nat}
    (hr : PolynomiallyBounded r) (hs : PolynomiallyBounded s) :
    PolynomiallyBounded (fun n => r n + s n) := by
  obtain ⟨c₁, k₁, hr⟩ := hr
  obtain ⟨c₂, k₂, hs⟩ := hs
  refine ⟨c₁ + c₂, max k₁ k₂, ?_⟩
  filter_upwards [hr, hs] with n hrn hsn
  have ht : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have hp₁ : (n + 1) ^ k₁ ≤ (n + 1) ^ (max k₁ k₂) :=
    Nat.pow_le_pow_right ht (le_max_left k₁ k₂)
  have hp₂ : (n + 1) ^ k₂ ≤ (n + 1) ^ (max k₁ k₂) :=
    Nat.pow_le_pow_right ht (le_max_right k₁ k₂)
  calc
    r n + s n ≤ c₁ * (n + 1) ^ k₁ + c₂ * (n + 1) ^ k₂ :=
      Nat.add_le_add hrn hsn
    _ ≤ c₁ * (n + 1) ^ (max k₁ k₂) +
        c₂ * (n + 1) ^ (max k₁ k₂) :=
      Nat.add_le_add (Nat.mul_le_mul_left c₁ hp₁) (Nat.mul_le_mul_left c₂ hp₂)
    _ = (c₁ + c₂) * (n + 1) ^ (max k₁ k₂) := by rw [Nat.add_mul]

theorem mul {r s : Nat → Nat}
    (hr : PolynomiallyBounded r) (hs : PolynomiallyBounded s) :
    PolynomiallyBounded (fun n => r n * s n) := by
  obtain ⟨c₁, k₁, hr⟩ := hr
  obtain ⟨c₂, k₂, hs⟩ := hs
  refine ⟨c₁ * c₂, k₁ + k₂, ?_⟩
  filter_upwards [hr, hs] with n hrn hsn
  calc
    r n * s n ≤ (c₁ * (n + 1) ^ k₁) * (c₂ * (n + 1) ^ k₂) :=
      Nat.mul_le_mul hrn hsn
    _ = (c₁ * c₂) * ((n + 1) ^ k₁ * (n + 1) ^ k₂) := by ac_rfl
    _ = (c₁ * c₂) * (n + 1) ^ (k₁ + k₂) := by rw [pow_add]

end PolynomiallyBounded
