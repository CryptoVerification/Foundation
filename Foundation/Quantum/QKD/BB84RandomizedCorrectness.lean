import Foundation.Quantum.QKD.BB84Randomized

/-! Raw-key correctness of the actual randomized, zero-tolerance experiment.
The bound averages the verified sampling bound over both basis strings and
private inputs. It is not a secrecy or error-corrected finite-key theorem. -/
namespace Foundation.Quantum.QKD.Randomized
noncomputable section
open Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

def seedOutcome {n : Nat} {e : Space} (A : BlockAttack n e) (s : Seed n)
    (k minKey tolerance : Nat) : ProbComp (RawProtocol.Output n) :=
  (testDistribution s k).bind (fun T => (A.outcome s.alice s.bob s.bits).map
    (fun r => rawOutput ⟨s,T⟩ k minKey tolerance (blockOutcomeBits n r)))

theorem outcome_seed {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    outcome A k minKey tolerance = (seedDistribution n).bind (fun s => seedOutcome A s k minKey tolerance) := by
  unfold outcome configurationDistribution
  rw [PMF.bind_bind]
  congr 1
  funext s
  rw [PMF.bind_map]
  rfl

theorem seedOutcome_valid {n : Nat} {e : Space} (A : BlockAttack n e) (s : Seed n)
    (k minKey tolerance : Nat) (hk : k ≤ (RawProtocol.matched s.alice s.bob).card) :
    seedOutcome A s k minKey tolerance =
      (RawProtocol.sampledOutcomes A s.alice s.bob s.bits k hk).map
        (fun r => RawProtocol.output s.alice s.bob s.bits (blockOutcomeBits n r.1) r.2 minKey tolerance) := by
  unfold seedOutcome testDistribution
  rw [dif_pos hk]
  unfold PMF.map
  rw [PMF.bind_comm]
  unfold RawProtocol.sampledOutcomes
  rw [PMF.bind_bind]
  congr 1
  funext r
  rw [PMF.bind_map]
  congr 1
  funext T
  simp only [Function.comp_def, rawOutput, requiredLength, if_pos hk]

abbrev disagrees {n : Nat} (o : RawProtocol.Output n) : Prop := o.aliceKey ≠ o.bobKey

def seedCorrectnessBound {n : Nat} (s : Seed n) (k : Nat) : ℝ :=
  if k ≤ (RawProtocol.matched s.alice s.bob).card then
    (Sampling.missedErrorBound (RawProtocol.matched s.alice s.bob) k 1).toReal else 0

theorem seed_correctness {n : Nat} {e : Space} (A : BlockAttack n e) (s : Seed n)
    (k minKey : Nat) :
    (eventProb (seedOutcome A s k minKey 0) disagrees).toReal ≤ seedCorrectnessBound s k := by
  by_cases hk : k ≤ (RawProtocol.matched s.alice s.bob).card
  · rw [seedOutcome_valid A s k minKey 0 hk]
    unfold eventProb
    rw [PMF.toOuterMeasure_map_apply]
    have he : (fun r => RawProtocol.output s.alice s.bob s.bits (blockOutcomeBits n r.1) r.2 minKey 0) ⁻¹'
        {o | disagrees o} = {r | RawProtocol.keyMismatch s.alice s.bob s.bits minKey r} := rfl
    rw [he]
    change (eventProb (RawProtocol.sampledOutcomes A s.alice s.bob s.bits k hk)
      (RawProtocol.keyMismatch s.alice s.bob s.bits minKey)).toReal ≤ _
    rw [seedCorrectnessBound, if_pos hk]
    apply ENNReal.toReal_mono _ (RawProtocol.keyMismatch_bound A s.alice s.bob s.bits k minKey hk)
    apply ENNReal.div_ne_top (by simp)
    exact_mod_cast Nat.ne_zero_of_lt (Nat.choose_pos hk)
  · rw [seedCorrectnessBound, if_neg hk, seedOutcome, eventProb_bind_toReal]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro T _
    have he : (fun r => rawOutput ⟨s,T⟩ k minKey 0 (blockOutcomeBits n r)) ⁻¹' {o | disagrees o} = ∅ := by
      ext r
      obtain ⟨hA,hB⟩ := insufficient_empty_keys ⟨s,T⟩ k minKey 0 (blockOutcomeBits n r) hk
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, disagrees, hA, hB, ne_eq,
        not_true_eq_false, Set.mem_empty_iff_false]
    unfold eventProb
    rw [PMF.toOuterMeasure_map_apply, he]
    simp

def correctnessBound (n k : Nat) : ℝ :=
  ∑ s : Seed n, (seedDistribution n s).toReal * seedCorrectnessBound s k

/-- No conditioning on acceptance: abort yields equal empty keys. -/
theorem correctness {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey : Nat) :
    (eventProb (outcome A k minKey 0) disagrees).toReal ≤ correctnessBound n k := by
  rw [outcome_seed, eventProb_bind_toReal]
  apply Finset.sum_le_sum
  intro s _
  exact mul_le_mul_of_nonneg_left (seed_correctness A s k minKey) ENNReal.toReal_nonneg

/-- The same estimate holds for the physical classical-quantum output, retaining Eve's system. -/
theorem physical_correctness {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey : Nat) :
    (Foundation.Quantum.recordEvent (.tensor (qubits n) e)
      (fun r => disagrees ((Fintype.equivFin (RawProtocol.Output n)).symm r))).probability
      (record A k minKey 0) ≤ correctnessBound n k := by
  calc
    _ = (eventProb (outcome A k minKey 0) disagrees).toReal := record_event A k minKey 0 disagrees
    _ ≤ _ := correctness A k minKey


/-- A small-block estimate useful for verifying a concrete joint attack. -/
theorem two_signal_bound : correctnessBound 2 1 ≤ 1 / 2 := by
  have hs (s : Seed 2) : seedCorrectnessBound s 1 ≤ 1 / 2 := by
    have hc : (RawProtocol.matched s.alice s.bob).card ≤ 2 := by
      simpa using Finset.card_le_univ (RawProtocol.matched s.alice s.bob)
    have hcases : (RawProtocol.matched s.alice s.bob).card = 0 ∨
        (RawProtocol.matched s.alice s.bob).card = 1 ∨
        (RawProtocol.matched s.alice s.bob).card = 2 := by omega
    rcases hcases with h | h | h <;>
      norm_num [seedCorrectnessBound, Sampling.missedErrorBound, h]
  calc
    _ ≤ ∑ s : Seed 2, (seedDistribution 2 s).toReal * (1 / 2 : ℝ) :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hs s) ENNReal.toReal_nonneg)
    _ = _ := by rw [← Finset.sum_mul, Density.probability_weights, one_mul]

end
end Foundation.Quantum.QKD.Randomized
