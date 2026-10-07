import Foundation.Constructions.Symmetric.EncryptThenMAC.TableMAC
import Foundation.Constructions.Symmetric.EncryptThenMAC.OneBitEncryption
import Foundation.Constructions.Symmetric.EncryptThenMAC.Security
import Foundation.Crypto.Semantics.Machine.FiniteRandomness
import Mathlib.Data.Fintype.EquivFin

/-! Information-theoretic strong unforgeability of the two-row table for
at most one signing query. Both rows retain the actual native sampler law. -/
namespace Foundation.Symmetric.EncryptThenMAC.TableMAC
open Foundation.Probability CryptoOracle
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The native interleaved key decoder is a bijection, including width zero. -/
theorem splitKey_bijective (width : Nat) : Function.Bijective (@splitKey width) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b h
    apply List.ofFn_injective
    change a.toList = b.toList
    rw [← splitKey_encoding a, ← splitKey_encoding b, h]
  · simp only [Key, Bits, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    rw [show 2 * width = width + width by omega, pow_add]

noncomputable def keyEquiv (width : Nat) : Bits (2 * width) ≃ Key width :=
  Equiv.ofBijective splitKey (splitKey_bijective width)

theorem uniform_pair {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    (uniform α).bind (fun a => (uniform β).map (fun b => (a, b))) = uniform (α × β) :=
  Foundation.Probability.uniform_pair

/-- The two secret rows are independent uniform tags. -/
theorem keygen_independent (width : Nat → Nat) (n : Nat) :
    (scheme width).keygen n =
      (uniform (Bits (width n))).bind (fun first =>
        (uniform (Bits (width n))).map (fun second => (first, second))) := by
  rw [uniform_pair]
  exact Machine.uniform_map_equiv (keyEquiv (width n))

/-- Guessing a fixed uniform tag has probability exactly the inverse tag count. -/
theorem guess_probability (width : Nat) (tag : Bits width) :
    eventProb (uniform (Bits width)) (· = tag) = (2 ^ width : ℝ≥0∞)⁻¹ := by
  simpa [Bits] using Foundation.Probability.uniform_guess tag

/-- Fix the disclosed row and resample only the undisclosed row. -/
def rowKey {width : Nat} (request : Bool) (tag hidden : Bits width) : Key width :=
  if request then (hidden, tag) else (tag, hidden)

theorem keygen_rows (width : Nat → Nat) (n : Nat) (request : Bool) :
    (scheme width).keygen n =
      (uniform (Bits (width n))).bind (fun tag =>
        (uniform (Bits (width n))).map (rowKey request tag)) := by
  rw [keygen_independent]
  cases request
  · rfl
  · change _ = (uniform (Bits (width n))).bind (fun tag =>
        (uniform (Bits (width n))).bind (fun hidden => PMF.pure (hidden, tag)))
    rw [PMF.bind_comm]
    rfl

/-- Reusing the disclosed ciphertext cannot produce a fresh valid pair.
For the other ciphertext, the unobserved tag is still uniform. -/
theorem fresh_probability (width : Nat → Nat) (n : Nat) (request : Bool)
    (tag : Bits (width n)) (candidate : Bool × Bits (width n)) :
    eventProb (uniform (Bits (width n))) (fun hidden =>
      macWins OneBitEncryption.scheme (scheme width) (rowKey request tag hidden)
        (candidate, [(request, tag)])) ≤ (2 ^ (width n) : ℝ≥0∞)⁻¹ := by
  classical
  rcases candidate with ⟨ciphertext, candidateTag⟩
  cases request <;> cases ciphertext
  · simp [eventProb, macWins, scheme, rowKey, sign, eq_comm]
  · exact le_of_eq (by simpa [macWins, scheme, rowKey, sign, eq_comm] using guess_probability (width n) candidateTag)
  · exact le_of_eq (by simpa [macWins, scheme, rowKey, sign, eq_comm] using guess_probability (width n) candidateTag)
  · simp [eventProb, macWins, scheme, rowKey, sign, eq_comm]

/-- Averaging branches cannot exceed a bound valid for each branch. -/
theorem eventProb_bind_le {α β : Type*} (p : PMF α) (f : α → PMF β)
    (event : β → Prop) (bound : ℝ≥0∞)
    (h : ∀ a, eventProb (f a) event ≤ bound) :
    eventProb (p.bind f) event ≤ bound :=
  Foundation.Probability.eventProb_bind_le p f event bound h

noncomputable def zeroResult {width : Nat} (p : Program Bool (Bits width) (Bool × Bits width)) :
    PMF (Bool × Bits width) :=
  (p.run (fun _ _ => PMF.pure ((), fun _ => false)) ()).map Outcome.result

/-- A query-free continuation has no trace and cannot depend on the key. -/
theorem zero_run {width : Nat} (p : Program Bool (Bits width) (Bool × Bits width))
    (h : p.BoundedQueries 0) (oracle : Oracle Bool (Bits width) Unit) :
    p.run oracle () = (zeroResult p).map (fun candidate => ⟨candidate, (), []⟩) := by
  induction p with
  | done candidate => simp [Program.run, zeroResult, PMF.pure_map]
  | query request next ih => cases h
  | coin next ih =>
      cases h with
      | coin _ _ hNext =>
          rw [Program.run]
          simp_rw [ih _ (hNext _)]
          simp [zeroResult, Program.run, PMF.map_bind, PMF.map_comp, Function.comp_def]

theorem sign_uniform (width : Nat → Nat) (n : Nat) (ciphertext : Bool) :
    ((scheme width).keygen n).map (fun key => sign key ciphertext) = uniform (Bits (width n)) := by
  rw [keygen_rows width n ciphertext, PMF.map_bind]
  cases ciphertext <;>
    simp [PMF.map_comp, Function.comp_def, rowKey, sign, PMF.map_const, Function.const_def]

/-- With no disclosed row, a fixed valid-pair guess has exactly this chance. -/
theorem fixed_forgery_probability (width : Nat → Nat) (n : Nat)
    (candidate : Bool × Bits (width n)) :
    eventProb ((scheme width).keygen n) (fun key =>
      macWins OneBitEncryption.scheme (scheme width) key (candidate, [])) =
        (2 ^ (width n) : ℝ≥0∞)⁻¹ := by
  classical
  have h := congrArg (fun p => eventProb p (· = candidate.2)) (sign_uniform width n candidate.1)
  rw [guess_probability] at h
  simpa [eventProb, PMF.toOuterMeasure_map_apply, macWins, scheme, Set.indicator_apply, eq_comm] using h

noncomputable def forgeryGame (width : Nat → Nat) (n : Nat)
    (attack : MACAttack OneBitEncryption.scheme (scheme width) n) :
    PMF (MACRecord OneBitEncryption.scheme (scheme width) n) :=
  ((scheme width).keygen n).bind fun key =>
    (attack.run (signingOracle OneBitEncryption.scheme (scheme width) n key) ()).map
      (fun out => (key, signingRecord OneBitEncryption.scheme (scheme width) out))

noncomputable def forgeryProbability (width : Nat → Nat) (n : Nat)
    (attack : MACAttack OneBitEncryption.scheme (scheme width) n) : ℝ≥0∞ :=
  eventProb (forgeryGame width n attack)
    (fun record => macWins OneBitEncryption.scheme (scheme width) record.1 record.2)

theorem done_forgery (width : Nat → Nat) (n : Nat) (candidate : Bool × Bits (width n)) :
    forgeryProbability width n (.done candidate) = (2 ^ (width n) : ℝ≥0∞)⁻¹ := by
  unfold forgeryProbability forgeryGame
  simp only [Program.run, signingRecord, PMF.pure_map]
  change eventProb (((scheme width).keygen n).bind
      (PMF.pure ∘ fun key => (key, candidate, []))) _ = _
  rw [PMF.bind_pure_comp]
  simpa only [eventProb, PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq] using
    fixed_forgery_probability width n candidate

theorem query_game (width : Nat → Nat) (n : Nat) (request : Bool)
    (next : Bits (width n) → MACAttack OneBitEncryption.scheme (scheme width) n)
    (hNext : ∀ tag, (next tag).BoundedQueries 0) :
    forgeryGame width n (.query request next) =
      (uniform (Bits (width n))).bind (fun tag =>
        (uniform (Bits (width n))).bind (fun hidden =>
          (zeroResult (next tag)).map (fun candidate =>
            (rowKey request tag hidden, candidate, [(request, tag)])))) := by
  unfold forgeryGame
  rw [keygen_rows width n request, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  congr 1
  funext tag
  congr 1
  funext hidden
  cases request <;>
    simp only [Program.run, signingOracle, scheme, rowKey, sign, Bool.false_eq_true, ↓reduceIte, PMF.pure_bind]
  all_goals
    rw [zero_run _ (hNext tag)]
    simp [PMF.map_comp, Function.comp_def, signingRecord]

theorem query_forgery (width : Nat → Nat) (n : Nat) (request : Bool)
    (next : Bits (width n) → MACAttack OneBitEncryption.scheme (scheme width) n)
    (hNext : ∀ tag, (next tag).BoundedQueries 0) :
    forgeryProbability width n (.query request next) ≤ (2 ^ (width n) : ℝ≥0∞)⁻¹ := by
  unfold forgeryProbability
  rw [query_game width n request next hNext]
  apply eventProb_bind_le
  intro tag
  rw [show ((uniform (Bits (width n))).bind (fun hidden =>
      (zeroResult (next tag)).map (fun candidate =>
        (rowKey request tag hidden, candidate, [(request, tag)])))) =
      (zeroResult (next tag)).bind (fun candidate =>
        (uniform (Bits (width n))).map (fun hidden =>
          (rowKey request tag hidden, candidate, [(request, tag)]))) from PMF.bind_comm _ _ _]
  apply eventProb_bind_le
  intro candidate
  simpa only [eventProb, PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq] using
    fresh_probability width n request tag candidate

/-- All local coins and adaptive continuations are allowed. The bound is on
actual signing queries, not on the total number of computation steps. -/
theorem forgery_le (width : Nat → Nat) (n : Nat)
    (attack : MACAttack OneBitEncryption.scheme (scheme width) n)
    (h : attack.BoundedQueries 1) :
    forgeryProbability width n attack ≤ (2 ^ (width n) : ℝ≥0∞)⁻¹ := by
  induction attack with
  | done candidate => exact le_of_eq (done_forgery width n candidate)
  | query request next ih =>
      cases h with
      | query _ _ _ hNext => exact query_forgery width n request next hNext
  | coin next ih =>
      have hNext : ∀ bit, (next bit).BoundedQueries 1 := by cases h; assumption
      unfold forgeryProbability forgeryGame
      simp only [Program.run, PMF.map_bind]
      rw [PMF.bind_comm]
      apply eventProb_bind_le
      intro bit
      exact ih bit (hNext bit)

/-- The attacker distribution is sampled independently of the MAC key. -/
theorem macGame_as_bind (width : Nat → Nat) (n : Nat)
    (attacks : PMF (MACAttack OneBitEncryption.scheme (scheme width) n)) :
    macGame OneBitEncryption.scheme (scheme width) n attacks =
      attacks.bind (forgeryGame width n) := rfl

theorem mac_advantage_le (width : Nat → Nat) (n : Nat)
    (attacks : PMF (MACAttack OneBitEncryption.scheme (scheme width) n))
    (h : ∀ attack ∈ attacks.support, attack.BoundedQueries 1) :
    macAdvantage OneBitEncryption.scheme (scheme width) n attacks ≤ (2 ^ (width n) : ℝ≥0∞)⁻¹ := by
  unfold macAdvantage
  rw [macGame_as_bind]
  exact Foundation.Probability.eventProb_bind_le_of_support attacks (forgeryGame width n)
    (fun record => macWins OneBitEncryption.scheme (scheme width) record.1 record.2)
    _ (fun attack hAttack => forgery_le width n attack (h attack hAttack))

/-- Once encryption is exhausted, every subsequent public query fails and
therefore generates no signing query at all. -/
theorem exhausted_queries (width : Nat → Nat) (n : Nat) (key : Bool)
    (attack : IntegrityAttack OneBitEncryption.scheme (scheme width) n) :
    (reduceIntegrity OneBitEncryption.scheme (scheme width) key true attack).BoundedQueries 0 := by
  exact OneBitEncryption.oneUseContract.exhausted_queries (scheme width) n key attack

/-- Any finite source attack, even with many failed requests, yields a
reduction with at most one actual signing query. -/
theorem reduction_queries (width : Nat → Nat) (n : Nat) (key : Bool)
    (attack : IntegrityAttack OneBitEncryption.scheme (scheme width) n) :
    (reduceIntegrity OneBitEncryption.scheme (scheme width) key false attack).BoundedQueries 1 := by
  exact OneBitEncryption.oneUseContract.reduction_queries (scheme width) n key attack

theorem reduction_advantage_le (width : Nat → Nat) (n : Nat)
    (attack : IntegrityAttack OneBitEncryption.scheme (scheme width) n) :
    macAdvantage OneBitEncryption.scheme (scheme width) n
      (integrityReduction OneBitEncryption.scheme (scheme width) n attack) ≤
        (2 ^ (width n) : ℝ≥0∞)⁻¹ := by
  apply mac_advantage_le
  intro program hProgram
  rw [integrityReduction, PMF.mem_support_map_iff] at hProgram
  obtain ⟨key, _, he⟩ := hProgram
  subst program
  exact reduction_queries width n key attack

/-- Unconditional ciphertext integrity for the one-use composition. -/
theorem integrity_advantage (width : Nat → Nat) (n : Nat)
    (attack : IntegrityAttack OneBitEncryption.scheme (scheme width) n) :
    integrityAdvantage OneBitEncryption.scheme (scheme width) n attack ≤
      (2 ^ (width n) : ℝ≥0∞)⁻¹ :=
  (integrity_advantage_le OneBitEncryption.scheme (scheme width) n attack).trans
    (reduction_advantage_le width n attack)

end Foundation.Symmetric.EncryptThenMAC.TableMAC
