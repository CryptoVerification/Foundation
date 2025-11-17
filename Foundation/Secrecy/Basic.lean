import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Init
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Foundation.SymmetricEncryption
import Foundation.Secrecy.FiniteDistribution
import Foundation.Secrecy.Utils

namespace Secrecy

open SymmetricEncryption
open scoped BigOperators
open Function

variable {Key Msg Ciph : Type _}

section FiniteKeys

variable [Fintype Key] [DecidableEq Ciph]

/-- Number of keys that map a message `m` to a ciphertext `c`. -/
def ciphertextCount (scheme : SymmetricEncryption Key Msg Ciph) (m : Msg) (c : Ciph) : ℕ :=
  Fintype.card { k : Key // scheme.enc k m = c }

/-- A ciphertext occurs with positive count iff there exists a key hitting it. -/
lemma ciphertextCount_pos_iff (scheme : SymmetricEncryption Key Msg Ciph)
    (m : Msg) (c : Ciph) :
    0 < ciphertextCount scheme m c ↔ ∃ k : Key, scheme.enc k m = c := by
  classical
  have hCard :
      (0 < Fintype.card { k : Key // scheme.enc k m = c }) ↔
        Nonempty { k : Key // scheme.enc k m = c } :=
    Fintype.card_pos_iff
  constructor
  · intro hpos
    have hpos' :
        0 < Fintype.card { k : Key // scheme.enc k m = c } := by
      simpa [ciphertextCount] using hpos
    have hNonempty := hCard.mp hpos'
    rcases hNonempty with ⟨⟨k, hk⟩⟩
    exact ⟨k, hk⟩
  · intro hexists
    have hNonempty :
        Nonempty { k : Key // scheme.enc k m = c } := by
      rcases hexists with ⟨k, hk⟩
      exact ⟨⟨k, hk⟩⟩
    have hpos' :
        0 < Fintype.card { k : Key // scheme.enc k m = c } :=
      hCard.mpr hNonempty
    simpa [ciphertextCount] using hpos'

/-- Probability of obtaining ciphertext `c` when encrypting `m` with a uniform random key. -/
def ciphertextProbability (scheme : SymmetricEncryption Key Msg Ciph) (m : Msg) (c : Ciph) : ℚ :=
  (ciphertextCount scheme m c : ℚ) / Fintype.card Key

/-- Shannon perfect secrecy: ciphertext distributions do not depend on the plaintext. -/
def perfectSecrecy (scheme : SymmetricEncryption Key Msg Ciph) : Prop :=
  ∀ m₁ m₂ c, ciphertextProbability scheme m₁ c = ciphertextProbability scheme m₂ c

/-- Number of keys for which the adversary outputs `true` on the ciphertext of `m`. -/
def adversaryWinCount (scheme : SymmetricEncryption Key Msg Ciph) (adv : Ciph → Bool)
    (m : Msg) : ℕ :=
  Fintype.card { k : Key // adv (scheme.enc k m) = true }

/-- Probability that an adversary outputs `true` when given the ciphertext of `m`. -/
def adversaryWinProbability (scheme : SymmetricEncryption Key Msg Ciph) (adv : Ciph → Bool)
    (m : Msg) : ℚ :=
  (adversaryWinCount scheme adv m : ℚ) / Fintype.card Key

/-- Perfect indistinguishability: every adversary sees identical distributions for any messages. -/
def perfectIndistinguishability (scheme : SymmetricEncryption Key Msg Ciph) : Prop :=
  ∀ adv m₁ m₂,
    adversaryWinProbability scheme adv m₁ = adversaryWinProbability scheme adv m₂

section
section
variable {α : Type _} [DecidableEq α]

/-- Number of keys for which the adversary outputs value `a`. -/
def adversaryOutputCount (scheme : SymmetricEncryption Key Msg Ciph)
    (adv : Ciph → α) (m : Msg) (a : α) : ℕ :=
  Fintype.card { k : Key // adv (scheme.enc k m) = a }

end

variable {α : Type _} [DecidableEq α]

omit [DecidableEq Ciph] in
/-- Probability that the adversary outputs `a` when encrypting `m`. -/
def adversaryOutputProbability (scheme : SymmetricEncryption Key Msg Ciph)
    (adv : Ciph → α) (m : Msg) (a : α) : ℚ :=
  (adversaryOutputCount scheme adv m a : ℚ) / Fintype.card Key

omit [DecidableEq Ciph] in
lemma adversaryOutputProbability_eq_winProbability
    (scheme : SymmetricEncryption Key Msg Ciph) (adv : Ciph → α) (m : Msg) (a : α) :
    adversaryOutputProbability scheme adv m a =
      adversaryWinProbability scheme (fun c => decide (adv c = a)) m := by
  classical
  unfold adversaryOutputProbability adversaryWinProbability
  have hEquiv :
      { k : Key // decide (adv (scheme.enc k m) = a) = true } ≃
        { k : Key // adv (scheme.enc k m) = a } := by
    refine
      { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
    · intro k
      refine ⟨k.1, ?_⟩
      exact of_decide_eq_true k.property
    · intro k
      refine ⟨k.1, ?_⟩
      simp [k.property]
    · intro k
      ext
      rfl
    · intro k
      ext
      rfl
  have hCard := Fintype.card_congr hEquiv
  have hCount :
      adversaryOutputCount scheme adv m a =
        adversaryWinCount scheme (fun c => decide (adv c = a)) m := by
    unfold adversaryOutputCount adversaryWinCount
    simp
  simp [hCount]

end

omit [DecidableEq Ciph] in
lemma adversaryOutputCount_sum {α : Type _} [DecidableEq α] [Fintype α]
    (scheme : SymmetricEncryption Key Msg Ciph) (adv : Ciph → α) (m : Msg) :
    ∑ a, adversaryOutputCount scheme adv m a = Fintype.card Key := by
  classical
  have hσ :
      Fintype.card
          (Σ a : α, { k : Key // adv (scheme.enc k m) = a }) =
        ∑ a, adversaryOutputCount scheme adv m a := by
    simp [adversaryOutputCount, Fintype.card_sigma]
  have hEquiv :
      (Σ a : α, { k : Key // adv (scheme.enc k m) = a }) ≃ Key := by
    refine
      { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
    · intro p
      exact p.2.1
    · intro k
      exact ⟨adv (scheme.enc k m), ⟨k, rfl⟩⟩
    · intro p
      rcases p with ⟨a, ⟨k, hk⟩⟩
      ext <;> simp [hk]
    · intro k
      simp
  have hCard := Fintype.card_congr hEquiv
  simpa [hσ] using hCard

omit [DecidableEq Ciph] in
lemma adversaryOutputProbability_nonneg {α : Type _} [DecidableEq α]
    (scheme : SymmetricEncryption Key Msg Ciph) (adv : Ciph → α) (m : Msg) (a : α) :
    0 ≤ adversaryOutputProbability scheme adv m a := by
  classical
  have hNum : 0 ≤ (adversaryOutputCount scheme adv m a : ℚ) := by
    exact_mod_cast Nat.zero_le _
  have hDen : 0 ≤ (Fintype.card Key : ℚ) := by
    exact_mod_cast Nat.zero_le (Fintype.card Key)
  simpa [adversaryOutputProbability] using Rat.div_nonneg hNum hDen

section
variable [Nonempty Key]

omit [DecidableEq Ciph] in
lemma adversaryOutputProbability_sum {α : Type _} [DecidableEq α] [Fintype α]
    (scheme : SymmetricEncryption Key Msg Ciph) (adv : Ciph → α) (m : Msg) :
    ∑ a, adversaryOutputProbability scheme adv m a = 1 := by
  classical
  have hCount :=
    adversaryOutputCount_sum (scheme := scheme) (adv := adv) (m := m)
  have hCountCast :
      ((∑ a, adversaryOutputCount scheme adv m a : ℕ) : ℚ) =
        (Fintype.card Key : ℚ) := by
    exact_mod_cast hCount
  have hCast :
      (∑ a, (adversaryOutputCount scheme adv m a : ℚ)) =
        ((∑ a, adversaryOutputCount scheme adv m a : ℕ) : ℚ) :=
    sum_natCast (fun a => adversaryOutputCount scheme adv m a)
  have hDen : (Fintype.card Key : ℚ) ≠ 0 := by
    have hpos : 0 < Fintype.card Key := Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
  unfold adversaryOutputProbability
  have :
      (∑ a, (adversaryOutputCount scheme adv m a : ℚ) /
          Fintype.card Key) =
        ((∑ a, adversaryOutputCount scheme adv m a : ℕ) : ℚ) /
          Fintype.card Key := by
    simp [div_eq_mul_inv, sum_mul_right, hCast]
  simpa [this, hCountCast, hDen, div_eq_mul_inv]

private def keyCardinalityNeZero : (Fintype.card Key : ℚ) ≠ 0 := by
  have hpos : 0 < Fintype.card Key := Fintype.card_pos_iff.mpr inferInstance
  have hne : Fintype.card Key ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
  exact_mod_cast hne

lemma perfectSecrecy_iff_card (scheme : SymmetricEncryption Key Msg Ciph) :
    perfectSecrecy scheme ↔
      ∀ m₁ m₂ c,
        ciphertextCount scheme m₁ c = ciphertextCount scheme m₂ c := by
  classical
  constructor
  · intro h m₁ m₂ c
    have h' := h m₁ m₂ c
    have hCount : ciphertextCount scheme m₁ c = ciphertextCount scheme m₂ c := by
      simpa [ciphertextProbability, keyCardinalityNeZero] using h'
    exact hCount
  · intro h m₁ m₂ c
    have h' : (ciphertextCount scheme m₁ c : ℚ) = ciphertextCount scheme m₂ c := by
      exact_mod_cast h m₁ m₂ c
    simp [ciphertextProbability, h', div_eq_mul_inv]

omit [DecidableEq Ciph] in
lemma perfectIndistinguishability_iff_card
    (scheme : SymmetricEncryption Key Msg Ciph) :
    perfectIndistinguishability scheme ↔
      ∀ adv m₁ m₂,
        adversaryWinCount scheme adv m₁ = adversaryWinCount scheme adv m₂ := by
  classical
  constructor
  · intro h adv m₁ m₂
    have h' := h adv m₁ m₂
    have hCount :
        adversaryWinCount scheme adv m₁ = adversaryWinCount scheme adv m₂ := by
      simpa [adversaryWinProbability, keyCardinalityNeZero] using h'
    exact hCount
  · intro h adv m₁ m₂
    have h' :
        (adversaryWinCount scheme adv m₁ : ℚ) = adversaryWinCount scheme adv m₂ := by
      exact_mod_cast h adv m₁ m₂
    simp [adversaryWinProbability, h', div_eq_mul_inv]

end

section
variable [Fintype Ciph]

lemma adversaryWinCount_card_sigma
    (scheme : SymmetricEncryption Key Msg Ciph) (adv : Ciph → Bool) (m : Msg) :
    adversaryWinCount scheme adv m =
      Fintype.card
        (Σ c : { c : Ciph // adv c = true },
          { k : Key // scheme.enc k m = c }) := by
  classical
  refine Fintype.card_congr ?_
  refine
    { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
  · intro k
    refine ⟨⟨scheme.enc k m, k.property⟩, ⟨k, rfl⟩⟩
  · intro k
    rcases k with ⟨⟨c, hc⟩, ⟨k, hk⟩⟩
    refine ⟨k, ?_⟩
    simpa [hk] using hc
  · intro k
    rcases k with ⟨k, hk⟩
    simp
  · intro k
    rcases k with ⟨⟨c, hc⟩, ⟨k, hk⟩⟩
    cases hk
    simp

lemma adversaryWinCount_eq_sum
    (scheme : SymmetricEncryption Key Msg Ciph) (adv : Ciph → Bool) (m : Msg) :
    adversaryWinCount scheme adv m =
      ∑ c : { c : Ciph // adv c = true },
        ciphertextCount scheme m c.1 := by
  classical
  have hσ :=
    adversaryWinCount_card_sigma (scheme := scheme) (adv := adv) (m := m)
  have hCards :
      Fintype.card
          (Σ c : { c : Ciph // adv c = true },
            { k : Key // scheme.enc k m = c }) =
        ∑ c : { c : Ciph // adv c = true },
          Fintype.card { k : Key // scheme.enc k m = c.1 } :=
    (Fintype.card_sigma
      (α := fun c : { c : Ciph // adv c = true } =>
        { k : Key // scheme.enc k m = c }))
  have hσ' := hσ.trans hCards
  have hσ'' :
      adversaryWinCount scheme adv m =
        ∑ c : { c : Ciph // adv c = true },
          ciphertextCount scheme m c.1 := by
    calc
      adversaryWinCount scheme adv m =
          ∑ c : { c : Ciph // adv c = true },
            Fintype.card { k : Key // scheme.enc k m = c.1 } := hσ'
      _ = ∑ c : { c : Ciph // adv c = true },
            ciphertextCount scheme m c.1 := by
        simp [ciphertextCount]
  exact hσ''

end

section
variable [Nonempty Key]
variable [Fintype Msg] [Nonempty Msg]

/--
Deterministic perfect secrecy implies the key space is at least as large as the
message space.
-/
lemma perfectSecrecy_cardKey_ge_cardMsg
    (scheme : SymmetricEncryption Key Msg Ciph)
    (h : perfectSecrecy scheme) :
    Fintype.card Msg ≤ Fintype.card Key := by
  classical
  obtain ⟨m₀⟩ := (inferInstance : Nonempty Msg)
  obtain ⟨k₀⟩ := (inferInstance : Nonempty Key)
  let c₀ := scheme.enc k₀ m₀
  have hCount :=
    (perfectSecrecy_iff_card (scheme := scheme)).1 h
  have basePos :
      0 < ciphertextCount scheme m₀ c₀ := by
    have : ∃ k : Key, scheme.enc k m₀ = c₀ := ⟨k₀, rfl⟩
    exact (ciphertextCount_pos_iff (scheme := scheme) m₀ c₀).2 this
  have existsKey :
      ∀ m : Msg, ∃ k : Key, scheme.enc k m = c₀ := by
    intro m
    have hEq := hCount m m₀ c₀
    have hpos :
        0 < ciphertextCount scheme m c₀ := by
      simpa [hEq] using basePos
    exact (ciphertextCount_pos_iff (scheme := scheme) m c₀).1 hpos
  classical
  choose keyOf hk using existsKey
  have hInj : Function.Injective keyOf := by
    intro m₁ m₂ hEq
    apply (SymmetricEncryption.enc_injective (scheme := scheme) (k := keyOf m₁))
    have hEnc₁ : scheme.enc (keyOf m₁) m₁ = c₀ := hk m₁
    have hEnc₂ : scheme.enc (keyOf m₁) m₂ = c₀ := by
      simpa [hEq] using hk m₂
    simp [hEnc₁, hEnc₂]
  exact Fintype.card_le_of_injective keyOf hInj

end

section
variable [Fintype Msg]

/-- Probability an adversary outputs `a` when the plaintext is sampled from distribution `μ`. -/
def adversaryOutputProbabilityWithMessageDistribution
    (scheme : SymmetricEncryption Key Msg Ciph) (μ : FiniteDistribution Msg)
    {α : Type _} [DecidableEq α] (adv : Ciph → α) (a : α) : ℚ :=
  ∑ m, μ.prob m * adversaryOutputProbability scheme adv m a

section
variable [DecidableEq Msg]

omit [DecidableEq Ciph] in
lemma adversaryOutputProbabilityWithMessageDistribution_dirac
    {α : Type _} [DecidableEq α]
    (scheme : SymmetricEncryption Key Msg Ciph) (adv : Ciph → α)
    (m : Msg) (a : α) :
    adversaryOutputProbabilityWithMessageDistribution scheme
        (FiniteDistribution.dirac m) adv a =
      adversaryOutputProbability scheme adv m a := by
  classical
  simp [adversaryOutputProbabilityWithMessageDistribution,
    FiniteDistribution.dirac, Finset.mem_univ]

end

/-- Perfect imitatability: adversary outputs ignore the plaintext distribution. -/
def perfectImitatability
    (scheme : SymmetricEncryption Key Msg Ciph) : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (adv : Ciph → α),
    ∃ dist : FiniteDistribution α,
      ∀ μ : FiniteDistribution Msg, ∀ a,
        adversaryOutputProbabilityWithMessageDistribution scheme μ adv a =
          dist.prob a

end

end FiniteKeys


end Secrecy
