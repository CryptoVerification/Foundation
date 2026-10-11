import Foundation.Quantum.QKD.LinearHash

/-! Linear-hash collision primitives for studying classical authentication.

The tag of a message is a uniformly random binary matrix applied to the
message. Fixed distinct messages collide with probability exactly
`2^(-tag length)`. The matrix key has `message length * tag length` bits.
The acceptance lemmas below do not prove adaptive message-authentication
security: in particular the zero message has the publicly known zero tag.
A complete Wegman--Carter construction and its BB84 channel composition
remain separate obligations. -/
namespace Foundation.Quantum.QKD.Authentication
noncomputable section
open Foundation.Probability
open Foundation.Quantum.QKD.Hashing
set_option backward.isDefEq.respectTransparency false

variable {μ : Type} [Fintype μ] [DecidableEq μ] {ν : Type} [Fintype ν] [DecidableEq ν]

/-- A fresh authentication key: a uniformly random binary matrix. -/
abbrev Key (μ ν : Type) [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν] :=
  Seed μ ν

/-- The key distribution of one round. -/
abbrev keyPMF (μ ν : Type) [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν] :
    PMF (Key μ ν) :=
  uniform (Seed μ ν)

/-- The authentication tag of a message. -/
def tag (K : Key μ ν) (x : Bits μ) : Bits ν :=
  linearHash K x

/-- The key consumption of one round, in bits. -/
def keyBits (μ ν : Type) [Fintype μ] [Fintype ν] : ℕ :=
  Fintype.card μ * Fintype.card ν

/-- Verification accepts if and only if the tag matches. -/
abbrev verify (K : Key μ ν) (x : Bits μ) (t : Bits ν) : Prop :=
  tag K x = t

/-- An event that holds for every key has probability one. -/
theorem eventProb_of_all {ι : Type} [Fintype ι] (p : PMF ι) (P : ι → Prop)
    [DecidablePred P] (hP : ∀ i, P i) : eventProb p P = 1 := by
  have hs : {a : ι | P a} = Set.univ := Set.eq_univ_iff_forall.mpr hP
  have hcalc := calc
    eventProb p P = p.toOuterMeasure {a | P a} := rfl
    _ = p.toOuterMeasure Set.univ := by rw [hs]
    _ = ∑' a, (Set.univ : Set ι).indicator p a := PMF.toOuterMeasure_apply _ _
    _ = ∑' a, p a := by simp
    _ = 1 := p.tsum_coe
  exact hcalc

/-- An event contained in another is no more likely. -/
theorem eventProb_le {ι : Type} (p : PMF ι) {P Q : ι → Prop} (h : ∀ i, P i → Q i) :
    eventProb p P ≤ eventProb p Q := by
  refine p.toOuterMeasure.mono (fun i hi => ?_)
  simpa using h i hi

/-- Two accepted tags against the same value imply tag equality. -/
theorem verify_tags_of_eq (K : Key μ ν) {x x' : Bits μ} {t : Bits ν} (hx : verify K x t)
    (hx' : verify K x' t) : tag K x = tag K x' := by
  unfold verify at hx hx'
  rw [hx, hx']

/-- Fixed distinct messages collide under a uniform key with probability
exactly `2^(-tag length)`. -/
theorem forge_bound (x x' : Bits μ) (hxx' : x ≠ x') :
    (eventProb (keyPMF μ ν) (fun K => tag K x = tag K x')).toReal =
      1 / (2 : ℝ) ^ Fintype.card ν := by
  unfold tag keyPMF
  exact linear_collision x x' hxx'

/-- For fixed messages and a fixed tag, the joint event that both messages
verify against that tag has probability at most `2^(-tag length)`. This is
an unconditional joint-event bound, not a conditional forgery bound. -/
theorem forge_accepts (x x' : Bits μ) (t : Bits ν) (hxx' : x ≠ x') :
    (eventProb (keyPMF μ ν) (fun K => verify K x t ∧ verify K x' t)).toReal ≤
      1 / (2 : ℝ) ^ Fintype.card ν := by
  have hle : (eventProb (keyPMF μ ν) (fun K => verify K x t ∧ verify K x' t)).toReal ≤
      (eventProb (keyPMF μ ν) (fun K => tag K x = tag K x')).toReal :=
    ENNReal.toReal_mono (eventProb_ne_top _ _)
      (eventProb_le (keyPMF μ ν) (P := fun K => verify K x t ∧ verify K x' t)
        (Q := fun K => tag K x = tag K x') (fun K hh => verify_tags_of_eq K hh.1 hh.2))
  exact hle.trans (forge_bound x x' hxx').le

/-- Each fixed nonzero message has a uniform marginal tag distribution.
The zero message instead always has tag zero. -/
theorem tag_uniform_of_ne_zero (x : Bits μ) (hx : x ≠ 0) (z : Bits ν) :
    (eventProb (keyPMF μ ν) (fun K => tag K x = z)).toReal =
      1 / (2 : ℝ) ^ Fintype.card ν := by
  have h1 : (fun K : Key μ ν => tag K x = z) =
      (fun K : Key μ ν => (Matrix.mulVec.addMonoidHomLeft (m := ν) x) K = z) := by
    funext K; rfl
  rw [h1]
  have h2 := uniform_hom_fiber (Matrix.mulVec.addMonoidHomLeft (m := ν) x)
    (hash_difference_surjective x hx) z
  simpa [ZMod.card] using h2

/-- The tag is linear in the message. -/
theorem tag_add (K : Key μ ν) (x y : Bits μ) :
    tag K (x + y) = tag K x + tag K y := by
  unfold tag linearHash
  exact Matrix.mulVec_add _ _ _

/-- Reusing one key for two rounds is forgeable: given an authentic pair
`(x, tag K x)` and `(y, tag K y)`, the pair `(x + y, tag K x + tag K y)`
is accepted by the same key with probability one. The theorem does not
assert that `x + y` is distinct from both observed messages. -/
theorem reuse_forges (K : Key μ ν) (x y : Bits μ) (_hxy : x ≠ y) :
    verify K (x + y) (tag K x + tag K y) := by
  unfold verify
  rw [tag_add K x y]

/-- The forgery probability of the reuse attack. -/
theorem reuse_forge_prob (x y : Bits μ) (hxy : x ≠ y) :
    (eventProb (keyPMF μ ν) (fun K => verify K (x + y) (tag K x + tag K y))).toReal = 1 := by
  have hall : eventProb (keyPMF μ ν) (fun K => verify K (x + y) (tag K x + tag K y)) = 1 :=
    eventProb_of_all (keyPMF μ ν) (fun K => verify K (x + y) (tag K x + tag K y))
      (fun K => reuse_forges K x y hxy)
  rw [hall]
  exact ENNReal.toReal_one

end
end Foundation.Quantum.QKD.Authentication
