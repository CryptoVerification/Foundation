import Foundation.Quantum.QKD.UsefulBB84

/-! Nonvacuity checks for the concrete useful-key parameters. The sifting
law is the actual independent-basis law. Error-free classical outcomes
pass the specified raw acceptance guard on every eligible test subset.
This file does not identify a physical no-attack quantum experiment with
these error-free outcomes. -/
namespace Foundation.Quantum.QKD.UsefulBB84
noncomputable section
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

/-- The actual basis-sifting distribution permits enough retained positions
with probability at least one half whenever its cutoff is below the mean. -/
theorem sifting_eligible_half (n cutoff : ℕ) (hcut : 2 * cutoff ≤ n) :
    (eventProb (uniform (Finset (Fin n))) (fun M => cutoff ≤ M.card)).toReal ≥ 1 / 2 := by
  classical
  let p := uniform (Finset (Fin n))
  let f : Finset (Fin n) → ℝ := fun M => if cutoff ≤ M.card then 1 else 0
  let e : Finset (Fin n) ≃ Finset (Fin n) :=
    ⟨fun M => Mᶜ, fun M => Mᶜ, fun M => compl_compl M, fun M => compl_compl M⟩
  have hw (M : Finset (Fin n)) : (p M).toReal = (p Mᶜ).toReal := by
    simp [p, uniform, PMF.uniformOfFintype_apply]
  have hswap : (∑ M : Finset (Fin n), (p M).toReal * f Mᶜ) =
      ∑ M : Finset (Fin n), (p M).toReal * f M := by
    calc
      _ = ∑ M : Finset (Fin n), (p Mᶜ).toReal * f Mᶜ := by
        apply Finset.sum_congr rfl
        intro M _
        rw [hw]
      _ = _ := by simpa [e] using e.sum_comp (fun M => (p M).toReal * f M)
  have hlocal (M : Finset (Fin n)) : 1 ≤ f M + f Mᶜ := by
    have hcard : Mᶜ.card + M.card = n := by simp
    by_cases hm : cutoff ≤ M.card
    · simp only [f, if_pos hm]
      split_ifs <;> norm_num
    · have hc : cutoff ≤ Mᶜ.card := by omega
      simp [f, hm, hc]
  have hsum : 1 ≤ 2 * (∑ M : Finset (Fin n), (p M).toReal * f M) := by
    calc
      1 = ∑ M : Finset (Fin n), (p M).toReal := (Density.probability_weights p).symm
      _ ≤ ∑ M : Finset (Fin n), (p M).toReal * (f M + f Mᶜ) := by
        apply Finset.sum_le_sum
        intro M _
        simpa using mul_le_mul_of_nonneg_left (hlocal M) ENNReal.toReal_nonneg
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [hswap]
        ring
  rw [eventProb_toReal]
  have he : (∑ M : Finset (Fin n), if cutoff ≤ M.card then (p M).toReal else 0) =
      ∑ M : Finset (Fin n), (p M).toReal * f M := by
    apply Finset.sum_congr rfl
    intro M _
    by_cases hm : cutoff ≤ M.card <;> simp [f, hm]
  change (1 / 2 : ℝ) ≤ ∑ M : Finset (Fin n), if cutoff ≤ M.card then (p M).toReal else 0
  rw [he]
  linarith

theorem sifting_eligible :
    (eventProb (uniform (Finset (Fin signals))) (fun M => tests + minKey ≤ M.card)).toReal ≥ 1 / 2 :=
  sifting_eligible_half signals (tests + minKey) (by decide)

/-- Every eligible noiseless raw record passes the existing protocol guard;
neither the test set nor the transmitted bit string is specially chosen. -/
theorem error_free_raw_accepts (M T : Finset (Fin signals)) (hT : T ⊆ M)
    (hcard : T.card = tests) (hm : tests + minKey ≤ M.card)
    (θ : Fin signals → BB84Basis) (b : Fin signals → Fin 2) :
    RawProtocol.accepts θ (BB84SiftingRandomness.bobBases θ M) b b T
      (BB84SiftingRandomness.requiredLength M tests minKey) 0 = true := by
  have hk : tests ≤ M.card := by omega
  unfold BB84SiftingRandomness.requiredLength
  rw [if_pos hk]
  unfold RawProtocol.accepts RawProtocol.keyPositions RawProtocol.errors
  rw [BB84SiftingRandomness.matched_bob]
  have hrem : (M \ T).card = M.card - tests := by
    rw [Finset.card_sdiff_of_subset hT, hcard]
  simp [hT, hrem, show minKey ≤ M.card - tests by omega]

/-- The noiseless raw keys agree on every such record. -/
theorem error_free_raw_keys_agree (M T : Finset (Fin signals))
    (θ : Fin signals → BB84Basis) (b : Fin signals → Fin 2) :
    (RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b b T minKey 0).aliceKey =
    (RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b b T minKey 0).bobKey :=
  RawProtocol.raw_keys_agree _ _ _ _ _ _ _ (by intros; rfl)

private theorem error_free_local_decode {m : ℕ} (θ : Fin m → BB84Basis)
    (b : Fin m → Fin 2) (T : Finset (Fin m)) (min : ℕ)
    (ha : RawProtocol.accepts θ θ b b T min 0 = true) :
    RawReconciliation.bobKey T (RawProtocol.output θ θ b b T min 0) =
      (RawProtocol.output θ θ b b T min 0).aliceKey := by
  let x := (PairwisePhaseCoordinates.testEquiv T (writeBits m b)).1
  have hkey : (RawProtocol.output θ θ b b T min 0).aliceKey =
      PairwisePhaseCoordinates.optionalKey T x := by
    dsimp [x]
    rw [PairwisePhaseCoordinates.optionalKey_split]
    funext i
    simp [RawProtocol.output, ha, RawProtocol.keyPositions, RawProtocol.matched, read_write]
  have hb : (RawProtocol.output θ θ b b T min 0).bobKey =
      (RawProtocol.output θ θ b b T min 0).aliceKey := by
    rfl
  unfold RawReconciliation.bobKey RawReconciliation.message
  rw [hb, hkey, RawReconciliation.remaining_optional]
  have hdec : ArbitraryReconciliation.quantumDecode x (ArbitraryReconciliation.quantumMessage x) = x :=
    ArbitraryReconciliation.quantum_correct x x (by intro j; simp [RepetitionReconciliation.errors])
  rw [hdec]

/-- Error-free eligible records also pass every verification hash after the
actual full-position reconciliation decoder. -/
theorem error_free_verification (M T : Finset (Fin signals)) (hT : T ⊆ M)
    (hcard : T.card = tests) (hm : tests + minKey ≤ M.card)
    (θ : Fin signals → BB84Basis) (b : Fin signals → Fin 2)
    (s : Hashing.RawSeed signals verificationBits) :
    Hashing.rawHash s (RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b b T minKey 0).aliceKey =
      Hashing.rawHash s (FullRawReconciliation.output
        (RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b b T minKey 0)).bobKey := by
  have ha := error_free_raw_accepts M T hT hcard hm θ b
  have hk : tests ≤ M.card := by omega
  simp only [BB84SiftingRandomness.requiredLength, if_pos hk] at ha
  have hs : RawProtocol.accepts (BB84SiftedInput.bases M θ) (BB84SiftedInput.bases M θ)
      (BB84SiftedInput.bits M b) (BB84SiftedInput.bits M b) (BB84SiftedInput.restrictTest M T) minKey 0 = true := by
    rw [← BB84SiftedInput.accepts_eq M T hT θ b b minKey 0]
    exact ha
  let o := RawProtocol.output (BB84SiftedInput.bases M θ) (BB84SiftedInput.bases M θ)
    (BB84SiftedInput.bits M b) (BB84SiftedInput.bits M b) (BB84SiftedInput.restrictTest M T) minKey 0
  have ho : BB84SiftedInput.restoreOutput M θ o =
      RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b b T minKey 0 :=
    BB84SiftedInput.restore_output M T hT θ b b minKey 0
  rw [← ho, FullRawReconciliation.bobKey_restore]
  have hdec : RawReconciliation.bobKey o.transcript.tested o = o.aliceKey :=
    error_free_local_decode _ _ _ _ hs
  rw [hdec]
  rfl

/-- Noiseless classical records using the existing randomized sifting and
test-subset law and the actual raw-output constructor. -/
def errorFreeRecords (θ : Fin signals → BB84Basis) (b : Fin signals → Fin 2) :
    PMF (RawProtocol.Output signals) :=
  (uniform (Finset (Fin signals))).bind (fun M =>
    (BB84SiftingRandomness.testDistribution M tests).map (fun T =>
      RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b b T
        (BB84SiftingRandomness.requiredLength M tests minKey) 0))

/-- The specified classical acceptance and reconciliation/check algorithms
continue with probability at least one half on the error-free record model,
for every bit string, basis string and verification seed. -/
theorem error_free_records_success (θ : Fin signals → BB84Basis) (b : Fin signals → Fin 2)
    (s : Hashing.RawSeed signals verificationBits) :
    (eventProb (errorFreeRecords θ b) (fun o => o.transcript.accepted = true ∧
      Hashing.rawHash s o.aliceKey = Hashing.rawHash s (FullRawReconciliation.output o).bobKey)).toReal ≥ 1 / 2 := by
  classical
  unfold errorFreeRecords
  rw [eventProb_bind_toReal]
  have he (M : Finset (Fin signals)) :
      eventProb ((BB84SiftingRandomness.testDistribution M tests).map (fun T =>
        RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b b T
          (BB84SiftingRandomness.requiredLength M tests minKey) 0))
        (fun o => o.transcript.accepted = true ∧
          Hashing.rawHash s o.aliceKey = Hashing.rawHash s (FullRawReconciliation.output o).bobKey) =
      eventProb (BB84SiftingRandomness.testDistribution M tests) (fun T =>
        (RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b b T
          (BB84SiftingRandomness.requiredLength M tests minKey) 0).transcript.accepted = true ∧
        Hashing.rawHash s (RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b b T
          (BB84SiftingRandomness.requiredLength M tests minKey) 0).aliceKey =
        Hashing.rawHash s (FullRawReconciliation.output (RawProtocol.output θ
          (BB84SiftingRandomness.bobBases θ M) b b T
          (BB84SiftingRandomness.requiredLength M tests minKey) 0)).bobKey) := by
    unfold eventProb
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  simp_rw [he]
  have hbound : (eventProb (uniform (Finset (Fin signals))) (fun M => tests + minKey ≤ M.card)).toReal ≤
      ∑ M : Finset (Fin signals), (uniform (Finset (Fin signals)) M).toReal *
        (eventProb (BB84SiftingRandomness.testDistribution M tests) (fun T =>
          (RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b b T
            (BB84SiftingRandomness.requiredLength M tests minKey) 0).transcript.accepted = true ∧
          Hashing.rawHash s (RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b b T
            (BB84SiftingRandomness.requiredLength M tests minKey) 0).aliceKey =
          Hashing.rawHash s (FullRawReconciliation.output (RawProtocol.output θ
            (BB84SiftingRandomness.bobBases θ M) b b T
            (BB84SiftingRandomness.requiredLength M tests minKey) 0)).bobKey)).toReal := by
    rw [eventProb_toReal]
    apply Finset.sum_le_sum
    intro M _
    by_cases hm : tests + minKey ≤ M.card
    · rw [if_pos hm]
      have hk : tests ≤ M.card := by omega
      have hprob : eventProb (BB84SiftingRandomness.testDistribution M tests) (fun T =>
          (RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b b T
            (BB84SiftingRandomness.requiredLength M tests minKey) 0).transcript.accepted = true ∧
          Hashing.rawHash s (RawProtocol.output θ (BB84SiftingRandomness.bobBases θ M) b b T
            (BB84SiftingRandomness.requiredLength M tests minKey) 0).aliceKey =
          Hashing.rawHash s (FullRawReconciliation.output (RawProtocol.output θ
            (BB84SiftingRandomness.bobBases θ M) b b T
            (BB84SiftingRandomness.requiredLength M tests minKey) 0)).bobKey) = 1 := by
        unfold eventProb
        apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
        intro T hT
        rw [BB84SiftingRandomness.testDistribution, dif_pos hk] at hT
        simp only [Sampling.sample, PMF.mem_support_uniformOfFinset_iff] at hT
        have hsub := (Finset.mem_powersetCard.mp hT).1
        have hcard := (Finset.mem_powersetCard.mp hT).2
        constructor
        · exact error_free_raw_accepts M T hsub hcard hm θ b
        · simp only [BB84SiftingRandomness.requiredLength, if_pos hk]
          exact error_free_verification M T hsub hcard hm θ b s
      rw [hprob]
      simp
    · rw [if_neg hm]
      positivity
  exact sifting_eligible.trans hbound

/-- Combined numerical safety and nonvacuous sifting eligibility. The
availability component is the basis-sifting law; physical honest-run
completeness is a separate statement. -/
theorem secure_with_eligible_sifting {e : Space} (A : BlockAttack signals e) :
    IdealKey.Secure (FullReconciledSecurity.realState (tag := verificationBits) (length := outputBits)
      A tests minKey 0) securityError ∧
    0 < outputBits ∧
    (eventProb (uniform (Finset (Fin signals))) (fun M => tests + minKey ≤ M.card)).toReal ≥ 1 / 2 :=
  ⟨secure A, output_positive, sifting_eligible⟩

end
end Foundation.Quantum.QKD.UsefulBB84
