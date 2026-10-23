import Foundation.Crypto.Semantics.Oracle.InteractionEncoding

/-! Scope diagnostic: a bijection selected from the secret is not a fixed
bijective state representation. Dropping that selection can erase the secret.
Retaining the selected codec repairs the correspondence explicitly. This is
not a separation from ordinary relational proofs that retain the same data. -/
namespace CryptoOracle.ProofEdits.Interaction.Encoding.Adaptive
open Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

def flip : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

def chosen (secret : Bool) : Unit → Bool ≃ Bool := fun _ => if secret then flip else Equiv.refl _

def plain (secret : Bool) : State Unit Bool := ⟨[], [], [], fun _ => secret⟩

def encode (original : State Unit Bool) : State Unit Bool :=
  state (chosen (original.function ())) original

theorem encode_plain (secret : Bool) : encode (plain secret) = plain false := by cases secret <;> rfl

theorem not_injective : ¬Function.Injective encode := by
  intro injective
  have same : encode (plain false) = encode (plain true) := by rw [encode_plain, encode_plain]
  have impossible := congrArg (fun original : State Unit Bool => original.function ()) (injective same)
  contradiction

theorem no_fixed_decoder : ¬∃ decode : State Unit Bool → Bool, ∀ secret, decode (encode (plain secret)) = secret := by
  rintro ⟨decode, correct⟩
  have left := correct false
  have right := correct true
  rw [encode_plain] at left right
  exact Bool.false_ne_true (left.symm.trans right)

/-- Each selected codec IS a bijection; the combined adaptive map is not. -/
def selectedEquivalence (secret : Bool) : State Unit Bool ≃ State Unit Bool := equivalence (chosen secret)

theorem selected_matches (secret : Bool) : selectedEquivalence secret (plain secret) = encode (plain secret) := rfl

theorem encoded_law : (uniform Bool).map (fun secret => encode (plain secret)) = PMF.pure (plain false) := by
  simp_rw [encode_plain]
  exact PMF.map_const _ _

theorem encoded_secret_law :
    ((uniform Bool).map (fun secret => encode (plain secret))).map (fun stored => stored.function ()) = PMF.pure false := by
  rw [encoded_law, PMF.pure_map]
  rfl

theorem encoded_secret_not_uniform :
    ((uniform Bool).map (fun secret => encode (plain secret))).map (fun stored => stored.function ()) ≠ uniform Bool := by
  rw [encoded_secret_law]
  intro same
  have atTrue := congrArg (fun distribution : PMF Bool => distribution true) same
  norm_num [uniform, PMF.pure_apply] at atTrue
  have nonzero : (2 : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  exact nonzero atTrue.symm

/-- Keep the actual selected codec as a correspondence coordinate. It is
not resampled or replaced with an independently chosen mask. -/
def retain (secret : Bool) : (Unit → Bool ≃ Bool) × State Unit Bool :=
  (chosen secret, encode (plain secret))

def decodeRetained (saved : (Unit → Bool ≃ Bool) × State Unit Bool) : Bool :=
  (saved.1 ()).symm (saved.2.function ())

theorem decode_retain (secret : Bool) : decodeRetained (retain secret) = secret := by cases secret <;> rfl

theorem retained_injective : Function.Injective retain := by
  intro left right same
  simpa only [decode_retain] using congrArg decodeRetained same

/-- The original secret and the decoded response keep their selected
joint law, rather than merely having individually uniform marginals. -/
theorem retained_joint :
    (uniform Bool).map (fun secret => (secret, decodeRetained (retain secret))) =
      (uniform Bool).map (fun secret => (secret, secret)) := by simp_rw [decode_retain]

end CryptoOracle.ProofEdits.Interaction.Encoding.Adaptive
