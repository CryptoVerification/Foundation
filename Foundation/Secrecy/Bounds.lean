import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Foundation.SymmetricEncryption
import Foundation.Secrecy.Basic

namespace Secrecy

open SymmetricEncryption
open scoped BigOperators

variable {Key Msg Ciph : Type _}

section CollisionBound

variable [Fintype Key] [Fintype Msg] [DecidableEq Ciph]
variable [Nonempty Key]

open scoped BigOperators

/-- For a fixed message `m`, count the keys mapping it to ciphertext `c`. -/
def messageCiphertextCount (scheme : SymmetricEncryption Key Msg Ciph)
    (m : Msg) (c : Ciph) : ℕ :=
  Fintype.card { k : Key // scheme.enc k m = c }

/-- Keys that map `m₀` to whatever ciphertext `m₁` produces under some key. -/
def overlapSet (scheme : SymmetricEncryption Key Msg Ciph)
    (m₀ m₁ : Msg) : Set Key :=
  { k : Key | ∃ k' : Key, scheme.enc k m₀ = scheme.enc k' m₁ }

lemma overlap_set_card_le (scheme : SymmetricEncryption Key Msg Ciph)
    (m₀ m₁ : Msg) :
    Fintype.card { k : Key // k ∈ overlapSet (scheme := scheme) m₀ m₁ } ≤
      Fintype.card Key := by
  classical
  exact Fintype.card_subtype_le _

/-- Number of keys whose ciphertext on `m₀` collides with some ciphertext of `m₁`. -/
def overlapCount (scheme : SymmetricEncryption Key Msg Ciph) (m₀ m₁ : Msg) : ℕ :=
  Fintype.card { k : Key // ∃ k' : Key, scheme.enc k m₀ = scheme.enc k' m₁ }

lemma overlapCount_le_keyCard (scheme : SymmetricEncryption Key Msg Ciph)
    (m₀ m₁ : Msg) :
    overlapCount scheme m₀ m₁ ≤ Fintype.card Key := by
  classical
  have :=
    overlap_set_card_le (scheme := scheme) (m₀ := m₀) (m₁ := m₁)
  exact this

/-- Keys whose ciphertext on `m₀` equals a fixed ciphertext. -/
def keySetForCipher (scheme : SymmetricEncryption Key Msg Ciph)
    (m₀ : Msg) (c : Ciph) : Set Key :=
  { k : Key | scheme.enc k m₀ = c }

lemma keySetForCipher_card_eq (scheme : SymmetricEncryption Key Msg Ciph)
    (m₀ : Msg) (c : Ciph) :
    Fintype.card { k : Key // k ∈ keySetForCipher (scheme := scheme) m₀ c } =
      messageCiphertextCount scheme m₀ c := by
  classical
  rfl

lemma overlapCount_eq_sum_cipherCount
    (scheme : SymmetricEncryption Key Msg Ciph) (m₀ m₁ : Msg) :
    overlapCount scheme m₀ m₁ =
      ∑ c : Ciph,
        messageCiphertextCount scheme m₀ c *
          messageCiphertextCount scheme m₁ c := by
  classical
  classical
  have hPartition :
      { k : Key // ∃ k' : Key, scheme.enc k m₀ = scheme.enc k' m₁ } ≃
        { p : Ciph × { k : Key // scheme.enc k m₀ = p.fst } ×
            { k : Key // scheme.enc k m₁ = p.fst } } := by
    refine
      { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
    · intro k
      classical
      rcases k with ⟨k, hk⟩
      rcases hk with ⟨k', hk'⟩
      refine
        ⟨scheme.enc k m₀,
          ⟨⟨k, rfl⟩, ⟨k', ?_⟩⟩⟩
      simpa using hk'
    · intro p
      classical
      rcases p with ⟨c, ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩⟩
      refine ⟨k, ?_⟩
      refine ⟨k', ?_⟩
      simp [hk, hk']
    · intro k
      classical
      ext <;> rfl
    · intro p
      classical
      rcases p with ⟨c, ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩⟩
      simp [hPartition]
  have hCard := Fintype.card_congr hPartition
  have hSum :
      overlapCount scheme m₀ m₁ =
        ∑ c : Ciph,
          (messageCiphertextCount scheme m₀ c *
            messageCiphertextCount scheme m₁ c) := by
    classical
    have :
        (∑ c : Ciph,
            messageCiphertextCount scheme m₀ c *
              messageCiphertextCount scheme m₁ c) =
          Fintype.card
            (Σ c : Ciph,
              { k : Key // scheme.enc k m₀ = c } ×
                { k : Key // scheme.enc k m₁ = c }) := by
      classical
      have hCardProd :
          ∀ c : Ciph,
            messageCiphertextCount scheme m₀ c *
                messageCiphertextCount scheme m₁ c =
              Fintype.card
                ({ k : Key // scheme.enc k m₀ = c } ×
                  { k : Key // scheme.enc k m₁ = c }) := by
        intro c
        simp [messageCiphertextCount, Fintype.card_eq.mpr (Equiv.refl _)]
      simpa [hCardProd]

/-- If messages are sampled from a small set, collisions are rare. -/
lemma exists_overlapCount_le_half
    (scheme : SymmetricEncryption Key Msg Ciph)
    (hCard :
      Fintype.card Msg = 2 * Fintype.card Key) :
    ∃ m₀ m₁ : Msg,
      overlapCount scheme m₀ m₁ ≤ Fintype.card Key / 2 := by
  classical
  admit

/-- Probability version of the bound. -/
lemma exists_overlapProbability_le_half
    (scheme : SymmetricEncryption Key Msg Ciph)
    (hCard :
      Fintype.card Msg = 2 * Fintype.card Key) :
    ∃ m₀ m₁ : Msg,
      overlapProbability scheme m₀ m₁ ≤ (1 : ℚ) / 2 := by
  classical
  admit

/-- Concrete bitstring statement. -/
theorem bitstring_overlapProbability_le_half
    (n : ℕ)
    (scheme :
      SymmetricEncryption (Fin n → ZMod 2) (Fin (n + 1) → ZMod 2) Ciph)
    [DecidableEq Ciph] :
    ∃ m₀ m₁ : Fin (n + 1) → ZMod 2,
      overlapProbability scheme m₀ m₁ ≤ (1 : ℚ) / 2 := by
  classical
  admit

end CollisionBound

end Secrecy
