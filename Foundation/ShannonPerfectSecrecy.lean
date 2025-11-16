import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Init
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Foundation.SymmetricEncryption

/-
Shannon perfect secrecy specific code lives in its own namespace so that the
common-key structure is decoupled from distributional properties.
-/
namespace ShannonPerfectSecrecy

open SymmetricEncryption
open scoped BigOperators

variable {Key Msg Ciph : Type _}

section FiniteKeys

variable [Fintype Key] [DecidableEq Ciph]

/-- Number of keys that map a message `m` to a ciphertext `c`. -/
def ciphertextCount (scheme : SymmetricEncryption Key Msg Ciph) (m : Msg) (c : Ciph) : ℕ :=
  Fintype.card { k : Key // scheme.enc k m = c }

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
variable [Nonempty Key]

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

private lemma adversaryWinCount_card_sigma
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

private lemma adversaryWinCount_eq_sum
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
variable [Nonempty Key] [Fintype Ciph]

theorem perfectSecrecy_iff_perfectIndistinguishability
    (scheme : SymmetricEncryption Key Msg Ciph) :
    perfectSecrecy scheme ↔ perfectIndistinguishability scheme := by
  classical
  constructor
  · intro h
    have hCount :=
      (perfectSecrecy_iff_card (scheme := scheme)).1 h
    refine
      (perfectIndistinguishability_iff_card (scheme := scheme)).2 ?_
    intro adv m₁ m₂
    have hTerm :
        ∀ c : { c : Ciph // adv c = true },
          ciphertextCount scheme m₁ c.1 = ciphertextCount scheme m₂ c.1 := by
      intro c
      simpa using hCount m₁ m₂ c.1
    have hSum :
        (∑ c : { c : Ciph // adv c = true }, ciphertextCount scheme m₁ c.1) =
          ∑ c : { c : Ciph // adv c = true }, ciphertextCount scheme m₂ c.1 := by
      simpa using congrArg
        (fun f :
            { c : Ciph // adv c = true } → ℕ =>
              ∑ c : { c : Ciph // adv c = true }, f c) (funext hTerm)
    simpa [adversaryWinCount_eq_sum (scheme := scheme)] using hSum
  · intro h
    have hCount :=
      (perfectIndistinguishability_iff_card (scheme := scheme)).1 h
    refine
      (perfectSecrecy_iff_card (scheme := scheme)).2 ?_
    intro m₁ m₂ c₀
    classical
    let adv : Ciph → Bool := fun c => if c = c₀ then true else false
    have hAdv :
        adversaryWinCount scheme adv m₁ =
          adversaryWinCount scheme adv m₂ := hCount adv m₁ m₂
    have hWin :
        ∀ m, adversaryWinCount scheme adv m = ciphertextCount scheme m c₀ := by
      intro m
      unfold adversaryWinCount ciphertextCount
      simp [adv]
    have hWin₁ := hWin m₁
    have hWin₂ := hWin m₂
    simpa [hWin₁, hWin₂] using hAdv

end

end FiniteKeys

end ShannonPerfectSecrecy
