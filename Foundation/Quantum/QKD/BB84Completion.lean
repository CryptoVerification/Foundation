import Foundation.Quantum.QKD.HonestBB84
import Foundation.Quantum.TraceDistanceNorm

/-! Standard half-trace-distance security and physical honest-run availability
for the actual full reconciled BB84 output, including both public seeds. -/
namespace Foundation.Quantum.QKD
noncomputable section
open Subnormalized Foundation.Probability
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

theorem IdealKey.secure_iff_traceDistance {T : Type} [Fintype T] {length : Nat} {e : Space}
    (ρ : Density (.tensor (IdealKey.register T length) e)) (ε : ℝ) :
    IdealKey.Secure ρ ε ↔ Density.traceDistance ρ (IdealKey.idealize ρ) ≤ ε :=
  Density.stateApprox_iff_traceDistance_le _ _ _

theorem readDensity_event {X : Type} [Fintype X] {e : Space}
    (ρ : Density (.tensor (.register (Fintype.card X)) e)) (P : X → Prop) [DecidablePred P] :
    mass (restrict (readDensity ρ) P) =
      (recordEvent e (fun r => P ((Fintype.equivFin X).symm r))).probability ρ := by
  rw [mass_restrict, recordEvent_probability, ← (Fintype.equivFin X).sum_comp]
  simp only [Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs
  · rfl
  · rfl

theorem discardMiddle_event {m : Nat} (b e : Space)
    (ρ : Density (.tensor (.register m) (.tensor b e))) (P : Fin m → Prop) [DecidablePred P] :
    (recordEvent e P).probability ((discardMiddle (.register m) b e).run ρ) =
      (recordEvent (.tensor b e) P).probability ρ := by
  rw [recordEvent_probability, recordEvent_probability]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · congr 1
    change (∑ u : e.Basis, (discardMiddle (.register m) b e).toKraus.apply ρ.matrix (r,u) (r,u)) = _
    calc
      _ = ∑ u : e.Basis, ∑ v : b.Basis, ρ.matrix (r,v,u) (r,v,u) :=
        Finset.sum_congr rfl (fun u _ => discardMiddle_apply (.register m) b e ρ.matrix r r u u)
      _ = _ := by
        change _ = ∑ p : b.Basis × e.Basis, ρ.matrix (r,p) (r,p)
        rw [Fintype.sum_prod_type, Finset.sum_comm]
  · rfl

theorem randomized_read_event {n : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) (P : RawProtocol.Output n → Prop) [DecidablePred P] :
    mass (restrict (readDensity (Randomized.keyState A k minKey tolerance)) P) =
      (eventProb (Randomized.outcome A k minKey tolerance) P).toReal := by
  rw [readDensity_event, Randomized.keyState, discardMiddle_event, Randomized.record_event]

theorem AcceptedAbort.acceptance_probability {T : Type} [Fintype T] [DecidableEq T]
    {length : Nat} {e : Space} (ρ : State (AcceptedAbort.AcceptedLabel T length) e)
    (σ : State T e) (h : mass ρ + mass σ = 1) :
    (recordEvent e (fun r => ((Fintype.equivFin (IdealKey.Output T length)).symm r).accepted = true)).probability
      (AcceptedAbort.state ρ σ h) = mass ρ := by
  unfold Effect.probability
  change ((recordEvent e _).matrix * (joint (relabel ρ AcceptedAbort.acceptLabel) +
    joint (relabel σ (AcceptedAbort.abortLabel (length := length))))).trace.re = _
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  rw [relabel_event_observation (ρ := ρ) (f := AcceptedAbort.acceptLabel) (P := fun o => o.accepted = true),
    relabel_event_observation (ρ := σ) (f := AcceptedAbort.abortLabel) (P := fun o => o.accepted = true)]
  simp [AcceptedAbort.acceptLabel, AcceptedAbort.abortLabel, mass]

theorem FullReconciledHash.acceptance_probability {n tag length : Nat} {e : Space}
    (ρ : State (RawProtocol.Output n) e) (h : mass ρ = 1) :
    (recordEvent e (fun r => ((Fintype.equivFin (IdealKey.Output (FullReconciledHash.Public n tag length)
      length)).symm r).accepted = true)).probability
      (FullReconciledHash.fullState (tag := tag) (length := length) ρ h) =
      ∑ s : Hashing.RawSeed n tag, (uniform (Hashing.RawSeed n tag) s).toReal *
        mass (restrict ρ (fun o => o.transcript.accepted = true ∧
          Hashing.rawHash s o.aliceKey = Hashing.rawHash s (FullRawReconciliation.output o).bobKey)) := by
  rw [FullReconciledHash.fullState, AcceptedAbort.acceptance_probability]
  unfold FullReconciledHash.bothAverage
  rw [VerifiedHash.mass_mixture]
  apply Finset.sum_congr rfl
  intro s _
  unfold FullReconciledHash.bothFixed
  rw [mass_relabel, mass_seed, restrict_intersection]

namespace UsefulBB84
local instance : Nonempty BB84Basis := ⟨.Z⟩

theorem secure_traceDistance {e : Space} (A : BlockAttack signals e) :
    Density.traceDistance (FullReconciledSecurity.realState (tag := verificationBits) (length := outputBits)
      A tests minKey 0) (IdealKey.idealize (FullReconciledSecurity.realState
        (tag := verificationBits) (length := outputBits) A tests minKey 0)) ≤ securityError :=
  (IdealKey.secure_iff_traceDistance _ _).mp (secure A)

theorem secure_half_traceNorm {e : Space} (A : BlockAttack signals e) :
    (1 / 2 : ℝ) * matrixTraceNorm
      ((FullReconciledSecurity.realState (tag := verificationBits) (length := outputBits)
        A tests minKey 0).matrix -
       (IdealKey.idealize (FullReconciledSecurity.realState
        (tag := verificationBits) (length := outputBits) A tests minKey 0)).matrix) ≤ securityError := by
  rw [← Density.traceDistance_eq_half_traceNorm]
  exact secure_traceDistance A

theorem honest_raw_success (s : Hashing.RawSeed signals verificationBits) :
    (eventProb (Randomized.outcome (HonestBB84.attack signals) tests minKey 0) (fun o =>
      o.transcript.accepted = true ∧
        Hashing.rawHash s o.aliceKey = Hashing.rawHash s (FullRawReconciliation.output o).bobKey)).toReal ≥ 1 / 2 := by
  rw [HonestBB84.outcome_eq_errorFreeRecords, eventProb_bind_toReal]
  calc
    _ ≥ ∑ p : (Fin signals → BB84Basis) × (Fin signals → Fin 2),
        (uniform _ p).toReal * (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_left (error_free_records_success p.1 p.2 s) ENNReal.toReal_nonneg
    _ = 1 / 2 := by rw [← Finset.sum_mul, Density.probability_weights, one_mul]

/-- The actual full quantum output accepts with probability at least one half
under identity transmission. Reconciliation, verification and PA are included. -/
theorem honest_success :
    (recordEvent .unit (fun r => ((Fintype.equivFin
      (IdealKey.Output (FullReconciledHash.Public signals verificationBits outputBits) outputBits)).symm r).accepted = true)).probability
      (FullReconciledSecurity.realState (tag := verificationBits) (length := outputBits)
        (HonestBB84.attack signals) tests minKey 0) ≥ 1 / 2 := by
  unfold FullReconciledSecurity.realState
  rw [FullReconciledHash.acceptance_probability]
  simp_rw [randomized_read_event]
  calc
    _ ≥ ∑ s : Hashing.RawSeed signals verificationBits, (uniform _ s).toReal * (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (honest_raw_success s) ENNReal.toReal_nonneg
    _ = 1 / 2 := by rw [← Finset.sum_mul, Density.probability_weights, one_mul]

end UsefulBB84

/-- A normalization check: orthogonal qubits have distance one, not two. -/
theorem traceDistance_orthogonal_qubits :
    Density.traceDistance (basisDensity .bit 0) (basisDensity .bit 1) = 1 := by
  apply le_antisymm (Density.traceDistance_le_one _ _)
  have h := Density.effect_le_traceDistance (basisDensity .bit 0) (basisDensity .bit 1) (basisEffect .bit 0)
  simpa [BB84Attack.basisEffect_probability, basisDensity] using h

end
end Foundation.Quantum.QKD
