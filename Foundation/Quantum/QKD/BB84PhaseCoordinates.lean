import Foundation.Quantum.QKD.BB84PurifiedSource
import Foundation.Quantum.QKD.QuantumSamplingLogic
import Foundation.Quantum.PartitionMeasurement

/-! Complementary coordinates of the actual purified BB84 source. The
sample records only the tested Alice/Bob bits and leaves all untested and
auxiliary coherences intact. Equivalence to the full sifting protocol's
phase-estimation experiment remains a separate obligation. -/
namespace Foundation.Quantum.QKD.BB84PhaseCoordinates
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev jointSpace (n : Nat) (e f : Space) :=
  Space.tensor (.tensor (.tensor (qubits n) e) f) (qubits n)

def gate (n : Nat) (e f : Space) : Operator (jointSpace n e f) :=
  Op.tensor (Op.tensor (Op.tensor (blockGate n (fun _ => .X)) (Op.ident e)) (Op.ident f))
    (blockGate n (fun _ => .X))

theorem isometry (n : Nat) (e f : Space) : (gate n e f).conjTranspose * gate n e f = 1 := by
  apply tensor_isometry
  · apply tensor_isometry
    · exact tensor_isometry _ _ (blockGate_isometry n _) (by simp [Op.ident])
    · simp [Op.ident]
  · exact blockGate_isometry n _

def channel (n : Nat) (e f : Space) : Channel (jointSpace n e f) (jointSpace n e f) :=
  Channel.ofIsometry (gate n e f) (isometry n e f)

def vector {n : Nat} {e : Space} (A : BlockAttack n e) : (BB84PurifiedSource.jointSpace A).Basis → ℂ :=
  (gate n e (.register (Fintype.card A.index))).mulVec (BB84PurifiedSource.vector A)

def state {n : Nat} {e : Space} (A : BlockAttack n e) : Density (BB84PurifiedSource.jointSpace A) :=
  (channel n e (.register (Fintype.card A.index))).run (BB84PurifiedSource.state A)

theorem pure {n : Nat} {e : Space} (A : BlockAttack n e) :
    (state A).matrix = PureProjection.rank (vector A) (vector A) := by
  change (Kraus.single (gate n e (.register (Fintype.card A.index)))).apply _ = _
  rw [BB84PurifiedSource.pure, Kraus.single_apply, SourceReplacement.rank_conjugate]
  rfl

theorem unit {n : Nat} {e : Space} (A : BlockAttack n e) :
    PureProjection.bracket (vector A) (vector A) = 1 := by
  have h := (state A).normalized
  rw [pure, PureProjection.rank_trace] at h
  exact h

def pattern {n : Nat} {e f : Space} (p : (jointSpace n e f).Basis) : Finset (Fin n) :=
  Finset.univ.filter (fun i => readBits p.1.1.1 i ≠ readBits p.2 i)

abbrev TestRecord (n : Nat) :=
  (Fin n → Option (Fin 2)) × (Fin n → Option (Fin 2))

def label {n : Nat} {e f : Space} (T : Finset (Fin n)) (p : (jointSpace n e f).Basis) : TestRecord n :=
  ((fun i => if i ∈ T then some (readBits p.2 i) else none),
   (fun i => if i ∈ T then some (readBits p.1.1.1 i) else none))

def accepts {n : Nat} (r : TestRecord n) : Prop := ∀ i, r.1 i = r.2 i
instance {n : Nat} : DecidablePred (accepts (n := n)) := fun _ => inferInstanceAs (Decidable (∀ _, _))

theorem label_eq_of_tested {n : Nat} {e f : Space} (T : Finset (Fin n))
    (p q : (jointSpace n e f).Basis)
    (ha : ∀ i ∈ T, readBits p.2 i = readBits q.2 i)
    (hb : ∀ i ∈ T, readBits p.1.1.1 i = readBits q.1.1.1 i) : label T p = label T q := by
  apply Prod.ext <;> funext i
  · by_cases hi : i ∈ T
    · simp only [label, if_pos hi, ha i hi]
    · simp only [label, if_neg hi]
  · by_cases hi : i ∈ T
    · simp only [label, if_pos hi, hb i hi]
    · simp only [label, if_neg hi]

theorem accepted_iff {n : Nat} {e f : Space} (T : Finset (Fin n)) (p : (jointSpace n e f).Basis) :
    accepts (label T p) ↔ Sampling.undetected (pattern p) T := by
  simp only [accepts, label, Sampling.undetected, Finset.disjoint_left, pattern,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h i hi
    have hh := h i
    simpa only [if_pos hi, Option.some.injEq, ne_eq, not_not, eq_comm] using hh
  · intro h i
    by_cases hi : i ∈ T
    · simpa only [if_pos hi, Option.some.injEq, eq_comm] using (not_not.mp (h hi))
    · simp only [if_neg hi]

def measurement {n : Nat} (e f : Space) (T : Finset (Fin n)) :
    Instrument (jointSpace n e f) (jointSpace n e f) (Fintype.card (TestRecord n)) :=
  PartitionMeasurement.instrument (fun p => Fintype.equivFin (TestRecord n) (label T p))

/-- Every matrix entry inside one observed sample fiber is preserved. In
particular no untested bit or auxiliary coordinate is measured here. -/
theorem measurement_entry {n : Nat} (e f : Space) (T : Finset (Fin n))
    (ρ : Operator (jointSpace n e f)) (r : TestRecord n) (i j : (jointSpace n e f).Basis) :
    ((measurement e f T).branch (Fintype.equivFin (TestRecord n) r)).apply ρ i j =
      if label T i = r ∧ label T j = r then ρ i j else 0 := by
  rw [measurement, PartitionMeasurement.branch_entry]
  simp only [Equiv.apply_eq_iff_eq]

theorem untested_coherence {n : Nat} (e f : Space) (T : Finset (Fin n))
    (ρ : Operator (jointSpace n e f)) (i j : (jointSpace n e f).Basis)
    (ha : ∀ k ∈ T, readBits i.2 k = readBits j.2 k)
    (hb : ∀ k ∈ T, readBits i.1.1.1 k = readBits j.1.1.1 k) :
    ((measurement e f T).branch (Fintype.equivFin (TestRecord n) (label T i))).apply ρ i j =
      ρ i j := by
  rw [measurement_entry]
  have h := label_eq_of_tested T i j ha hb
  rw [h, if_pos ⟨rfl,rfl⟩]

theorem acceptance_probability {n : Nat} (e f : Space) (T : Finset (Fin n))
    (ρ : Density (jointSpace n e f)) :
    (QuantumErrorTest.test (fun p => Sampling.undetected (pattern p) T)).probability ρ 0 =
      (recordEvent (jointSpace n e f) (fun r => accepts ((Fintype.equivFin (TestRecord n)).symm r))).probability
        ((measurement e f T).record.run ρ) := by
  have h := PartitionMeasurement.acceptance
    (fun p : (jointSpace n e f).Basis => Fintype.equivFin (TestRecord n) (label T p))
    (fun r => accepts ((Fintype.equivFin (TestRecord n)).symm r)) ρ
  simp only [Equiv.symm_apply_apply] at h
  simpa only [accepted_iff, measurement] using h

end
end Foundation.Quantum.QKD.BB84PhaseCoordinates
