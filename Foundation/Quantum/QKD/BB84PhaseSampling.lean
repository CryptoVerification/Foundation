import Foundation.Quantum.QKD.BB84PhaseCoordinates

/-! Quantum sampling instantiated on the complementary coordinates of an
arbitrary actual finite-Kraus BB84 attack. The constructed ideal state has
small phase-error support after a zero-error sample is accepted. -/
namespace Foundation.Quantum.QKD.BB84PhaseSampling
noncomputable section
open BB84PhaseCoordinates PureProjection
set_option backward.isDefEq.respectTransparency false

theorem joint_nonempty {n : Nat} {e : Space} (A : BlockAttack n e) :
    Nonempty (BB84PurifiedSource.jointSpace A).Basis := by
  classical
  by_contra h
  have : IsEmpty (BB84PurifiedSource.jointSpace A).Basis := not_nonempty_iff.mp h
  have hh := (state A).normalized
  norm_num [Matrix.trace, Matrix.diag] at hh

/-- A zero-error basis vector, using actual auxiliary coordinates from the
nonempty joint space. No positive probability for the good projection is assumed. -/
def fallback {n : Nat} {e : Space} (A : BlockAttack n e) : (BB84PurifiedSource.jointSpace A).Basis :=
  let p := Classical.choice (joint_nonempty A)
  (((writeBits n (fun _ => 0), p.1.1.2), p.1.2), writeBits n (fun _ => 0))

theorem fallback_pattern {n : Nat} {e : Space} (A : BlockAttack n e) : pattern (fallback A) = ∅ := by
  ext i
  simp [fallback, pattern]

theorem fallback_good {n : Nat} {e : Space} (A : BlockAttack n e)
    (U T : Finset (Fin n)) (bad : Nat) (hb : 0 < bad) :
    QuantumErrorSampling.good U bad pattern T (fallback A) := by
  simp only [QuantumErrorSampling.good, Sampling.badUndetected, fallback_pattern,
    Finset.empty_inter, Finset.card_empty]
  omega

theorem approximation {n : Nat} {e : Space} (A : BlockAttack n e)
    (U : Finset (Fin n)) (k bad : Nat) (hk : k ≤ U.card) :
    OperatorApprox (QuantumSampling.real (Sampling.sample U k hk) (vector A))
      (QuantumSampling.ideal (Sampling.sample U k hk)
        (QuantumErrorSampling.good U bad pattern) (vector A) (fun _ => fallback A))
      (Real.sqrt (Sampling.missedErrorBound U k bad).toReal) :=
  QuantumErrorSampling.approximation U k bad hk pattern (vector A) (unit A) (fun _ => fallback A)

/-- For every accepted ideal branch, all rows with at least `bad` errors in
the population vanish, including rows against arbitrary auxiliary coherences. -/
theorem accepted_zero_row {n : Nat} {e : Space} (A : BlockAttack n e)
    (U T : Finset (Fin n)) (bad : Nat) (hb : 0 < bad)
    (i j : (BB84PurifiedSource.jointSpace A).Basis) (hi : bad ≤ (pattern i ∩ U).card) :
    ((QuantumErrorTest.test (fun p => Sampling.undetected (pattern p) T)).branch 0).apply
      (SupportProjection.state (QuantumErrorSampling.good U bad pattern T)
        (vector A) (fallback A)).matrix i j = 0 :=
  QuantumErrorTest.accepted_zero_row U bad pattern T (vector A) (fallback A)
    (fallback_good A U T bad hb) i j hi

/-- The same support conclusion holds for every accepted detailed sample
record. The finer measurement is not replaced by the coarse test's state. -/
theorem accepted_measurement_zero_row {n : Nat} {e : Space} (A : BlockAttack n e)
    (U T : Finset (Fin n)) (bad : Nat) (hb : 0 < bad) (r : TestRecord n) (hr : accepts r)
    (i j : (BB84PurifiedSource.jointSpace A).Basis) (hi : bad ≤ (pattern i ∩ U).card) :
    ((measurement e (.register (Fintype.card A.index)) T).branch
      (Fintype.equivFin (TestRecord n) r)).apply
      (SupportProjection.state (QuantumErrorSampling.good U bad pattern T)
        (vector A) (fallback A)).matrix i j = 0 := by
  rw [measurement_entry]
  split_ifs with h
  · have ht : Sampling.undetected (pattern i) T := (accepted_iff T i).mp (h.1 ▸ hr)
    have hnot : ¬ QuantumErrorSampling.good U bad pattern T i :=
      not_not.mpr ⟨hi,ht⟩
    have hz := SupportProjection.supported (QuantumErrorSampling.good U bad pattern T)
      (vector A) (fallback A) (fallback_good A U T bad hb) i hnot
    change SupportProjection.vector _ _ _ i * star (SupportProjection.vector _ _ _ j) = 0
    rw [hz, zero_mul]
  · rfl

abbrev sampledSpace {n : Nat} {e : Space} (A : BlockAttack n e) :=
  Guessing.publicSpace (Finset (Fin n)) (BB84PurifiedSource.jointSpace A)

/-- The public sample and its two observed strings form one finite record.
Untested bit values and all auxiliary coordinates are absent from this label. -/
def publicLabel {n : Nat} {e : Space} (A : BlockAttack n e) (p : (sampledSpace A).Basis) :
    Fin (Fintype.card (Finset (Fin n) × TestRecord n)) :=
  Fintype.equivFin _ (let T := (Fintype.equivFin (Finset (Fin n))).symm p.1; (T, label T p.2))

def channels {n : Nat} {e : Space} (A : BlockAttack n e) :
    Nat → Channel (sampledSpace A) (sampledSpace A) :=
  fun _ => (PartitionMeasurement.instrument (publicLabel A)).forget

/-- Interpret the existing finite sampling derivation on the actual attack
vector. Its classical premise is proved by nonreplacement sampling, rather
than postulating the desired quantum estimate. -/
theorem interpreted {n : Nat} {e : Space} (A : BlockAttack n e)
    (U : Finset (Fin n)) (k bad : Nat) (hk : k ≤ U.card) :
    (QuantumSamplingLogic.model (Sampling.sample U k hk)
      (QuantumErrorSampling.good U bad pattern) (vector A) (unit A)
      (fun _ => fallback A) (channels A)).Carrier
      (.processed 0 (Real.sqrt (Sampling.missedErrorBound U k bad).toReal)) := by
  apply QuantumSamplingLogic.sound _ _ _ _ _ _
    (QuantumSamplingLogic.proof 0 (Sampling.missedErrorBound U k bad).toReal)
  intro _
  exact QuantumErrorSampling.classical U k bad hk pattern

theorem recorded {n : Nat} {e : Space} (A : BlockAttack n e)
    (U : Finset (Fin n)) (k bad : Nat) (hk : k ≤ U.card) :
    OperatorApprox ((PartitionMeasurement.instrument (publicLabel A)).record.toKraus.apply
      (QuantumSampling.real (Sampling.sample U k hk) (vector A)))
      ((PartitionMeasurement.instrument (publicLabel A)).record.toKraus.apply
        (QuantumSampling.ideal (Sampling.sample U k hk)
          (QuantumErrorSampling.good U bad pattern) (vector A) (fun _ => fallback A)))
      (Real.sqrt (Sampling.missedErrorBound U k bad).toReal) :=
  (approximation A U k bad hk).postprocess (PartitionMeasurement.instrument (publicLabel A)).record

end
end Foundation.Quantum.QKD.BB84PhaseSampling
