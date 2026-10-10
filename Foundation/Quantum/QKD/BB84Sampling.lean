import Foundation.Quantum.QKD.BB84RawProtocol
import Foundation.Quantum.QKD.SamplingBound

/-! Classical error sampling of the actual block measurement distribution.
The sampler is fresh and uniform after measurement. This does not identify
classical bit errors with quantum phase errors or prove secrecy. -/
namespace Foundation.Quantum.QKD.RawProtocol
noncomputable section
open Foundation.Probability
open scoped ENNReal

def errorPositions {n : Nat} (b c : Fin n → Fin 2) : Finset (Fin n) :=
  Finset.univ.filter (fun i => b i ≠ c i)

def errorDistribution {n : Nat} {e : Space} (A : BlockAttack n e)
    (alice bob : Fin n → BB84Basis) (b : Fin n → Fin 2) : ProbComp (Finset (Fin n)) :=
  (A.outcome alice bob b).map (fun r => errorPositions b (blockOutcomeBits n r))

/-- An arbitrary joint quantum attack followed by independently chosen tests. -/
def sampledErrors {n : Nat} {e : Space} (A : BlockAttack n e)
    (alice bob : Fin n → BB84Basis) (b : Fin n → Fin 2)
    (k : Nat) (hk : k ≤ (matched alice bob).card) : ProbComp (Finset (Fin n) × Finset (Fin n)) :=
  Sampling.experiment (errorDistribution A alice bob b) (matched alice bob) k hk

/-- Exact finite-population upper bound for missing all errors of a large error pattern. -/
theorem sampledErrors_bound {n : Nat} {e : Space} (A : BlockAttack n e)
    (alice bob : Fin n → BB84Basis) (b : Fin n → Fin 2)
    (k bad : Nat) (hk : k ≤ (matched alice bob).card) :
    eventProb (sampledErrors A alice bob b k hk)
      (Sampling.badUndetected (matched alice bob) bad) ≤
      Sampling.missedErrorBound (matched alice bob) k bad :=
  Sampling.experiment_bound _ _ _ _ _

theorem zero_errors_iff {n : Nat} (b c : Fin n → Fin 2) (T : Finset (Fin n)) :
    errors b c T = 0 ↔ Sampling.undetected (errorPositions b c) T := by
  simp only [errors, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Sampling.undetected,
    Finset.disjoint_left, errorPositions, Finset.mem_filter, Finset.mem_univ, true_and]
/-- This zero-tolerance acceptance check has the event bounded above. -/
theorem accepts_zero_undetected {n : Nat} (alice bob : Fin n → BB84Basis)
    (b c : Fin n → Fin 2) (T : Finset (Fin n)) (minKey : Nat)
    (h : accepts alice bob b c T minKey 0 = true) :
    Sampling.undetected (errorPositions b c) T := by
  apply (zero_errors_iff b c T).mp
  have hh : T ⊆ matched alice bob ∧ minKey ≤ (keyPositions alice bob T).card ∧
      errors b c T ≤ 0 := of_decide_eq_true h
  omega


/-- The actual measurement label and test mask, before encoding the public transcript. -/
def sampledOutcomes {n : Nat} {e : Space} (A : BlockAttack n e)
    (alice bob : Fin n → BB84Basis) (b : Fin n → Fin 2)
    (k : Nat) (hk : k ≤ (matched alice bob).card) :
    ProbComp (Fin (Fintype.card (qubits n).Basis) × Finset (Fin n)) :=
  (A.outcome alice bob b).bind (fun r =>
    (Sampling.sample (matched alice bob) k hk).map (fun T => (r,T)))

/-- Acceptance with zero observed errors despite at least `bad` actual bit errors. -/
def badAccepted {n : Nat} (alice bob : Fin n → BB84Basis) (b : Fin n → Fin 2)
    (minKey bad : Nat) (r : Fin (Fintype.card (qubits n).Basis) × Finset (Fin n)) : Prop :=
  accepts alice bob b (blockOutcomeBits n r.1) r.2 minKey 0 = true ∧
    bad ≤ (errorPositions b (blockOutcomeBits n r.1) ∩ matched alice bob).card

/-- This bounds the actual zero-tolerance raw protocol acceptance event without conditioning on acceptance. -/
theorem badAccepted_bound {n : Nat} {e : Space} (A : BlockAttack n e)
    (alice bob : Fin n → BB84Basis) (b : Fin n → Fin 2)
    (k minKey bad : Nat) (hk : k ≤ (matched alice bob).card) :
    eventProb (sampledOutcomes A alice bob b k hk) (badAccepted alice bob b minKey bad) ≤
      Sampling.missedErrorBound (matched alice bob) k bad := by
  apply eventProb_bind_le
  intro r
  unfold eventProb
  rw [PMF.toOuterMeasure_map_apply]
  by_cases hbad : bad ≤ (errorPositions b (blockOutcomeBits n r) ∩ matched alice bob).card
  · calc
      _ ≤ (Sampling.sample (matched alice bob) k hk).toOuterMeasure
          {T | Sampling.undetected (errorPositions b (blockOutcomeBits n r)) T} := by
        apply MeasureTheory.OuterMeasure.mono
        intro T hT
        exact accepts_zero_undetected alice bob b _ T minKey hT.1
      _ ≤ _ := Sampling.undetected_le _ _ _ _ _ hbad
  · have hs : (fun T => (r,T)) ⁻¹' {x | badAccepted alice bob b minKey bad x} = ∅ := by
      ext T
      simp [badAccepted, hbad]
    rw [hs]
    simp


/-- Unequal private raw keys imply acceptance and a genuine error among matched positions. -/
theorem unequal_keys_imply_badAccepted {n : Nat} (alice bob : Fin n → BB84Basis)
    (b : Fin n → Fin 2) (minKey : Nat)
    (r : Fin (Fintype.card (qubits n).Basis) × Finset (Fin n))
    (h : (output alice bob b (blockOutcomeBits n r.1) r.2 minKey 0).aliceKey ≠
      (output alice bob b (blockOutcomeBits n r.1) r.2 minKey 0).bobKey) :
    badAccepted alice bob b minKey 1 r := by
  constructor
  · cases ha : accepts alice bob b (blockOutcomeBits n r.1) r.2 minKey 0 with
    | false =>
      obtain ⟨hA,hB⟩ := abort_keys alice bob b _ r.2 minKey 0 ha
      exact False.elim (h (hA.trans hB.symm))
    | true => rfl
  · by_contra hc
    have hz : (errorPositions b (blockOutcomeBits n r.1) ∩ matched alice bob).card = 0 := by omega
    have he := Finset.card_eq_zero.mp hz
    apply h
    apply raw_keys_agree
    intro i hi
    by_contra hne
    have hiU : i ∈ matched alice bob := (Finset.mem_sdiff.mp hi).1
    have himem : i ∈ errorPositions b (blockOutcomeBits n r.1) ∩ matched alice bob := by
      simp [errorPositions, hne, hiU]
    rw [he] at himem
    exact Finset.notMem_empty i himem

/-- Unconditioned raw-key disagreement, with both keys empty on abort. -/
def keyMismatch {n : Nat} (alice bob : Fin n → BB84Basis) (b : Fin n → Fin 2)
    (minKey : Nat) (r : Fin (Fintype.card (qubits n).Basis) × Finset (Fin n)) : Prop :=
  (output alice bob b (blockOutcomeBits n r.1) r.2 minKey 0).aliceKey ≠
    (output alice bob b (blockOutcomeBits n r.1) r.2 minKey 0).bobKey

/-- A raw-key correctness estimate for the zero-tolerance test, before error correction.
It uses the exact combinatorial missed-error bound with one erroneous position. -/
theorem keyMismatch_bound {n : Nat} {e : Space} (A : BlockAttack n e)
    (alice bob : Fin n → BB84Basis) (b : Fin n → Fin 2)
    (k minKey : Nat) (hk : k ≤ (matched alice bob).card) :
    eventProb (sampledOutcomes A alice bob b k hk) (keyMismatch alice bob b minKey) ≤
      Sampling.missedErrorBound (matched alice bob) k 1 := by
  calc
    _ ≤ eventProb (sampledOutcomes A alice bob b k hk) (badAccepted alice bob b minKey 1) := by
      apply MeasureTheory.OuterMeasure.mono
      intro r hr
      exact unequal_keys_imply_badAccepted alice bob b minKey r hr
    _ ≤ _ := badAccepted_bound A alice bob b k minKey 1 hk

end
end Foundation.Quantum.QKD.RawProtocol
