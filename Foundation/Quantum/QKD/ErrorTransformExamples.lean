import Foundation.Quantum.QKD.BB84PreparedRawInterpretation
import Foundation.Quantum.QKD.SourceReplacementExamples

/-! A genuinely entangled three-qubit input and a closed finite derivation.
This is an independently constructed validation example, not a final-key
security claim or a product-state restriction on the general theorem. -/
namespace Foundation.Quantum.QKD.ErrorTransformExamples
noncomputable section
open Foundation.Logic PureProjection BB84ErrorTransform
set_option backward.isDefEq.respectTransparency false

abbrev pairSpace := Space.tensor (qubits 1) (qubits 1)
abbrev jointSpace := Space.tensor pairSpace .bit

def vector (p : jointSpace.Basis) : ℂ :=
  if p.1.1.1 = p.1.2.1 ∧ p.1.2.1 = p.2 then hadamardCoefficient else 0

theorem unit : bracket vector vector = 1 := by
  change (∑ p : ((Fin 2 × Unit) × (Fin 2 × Unit)) × Fin 2,
    star (vector p) * vector p) = 1
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_unique]
  norm_num [vector, starRingEnd_apply, hadamardCoefficient_square]

def state : Density jointSpace := pure vector unit

theorem input_coherence :
    state.matrix (((0,()),(0,())),0) (((1,()),(1,())),1) = 1/2 := by
  norm_num [state, PureProjection.pure, rank, Matrix.vecMulVec_apply, Pi.star_apply, vector,
    starRingEnd_apply, hadamardCoefficient_square]

def gate : Op jointSpace jointSpace :=
  Op.tensor (basisGate 1 (fun _ => .X)) (Op.ident .bit)

theorem amplitude (u : Fin 2) :
    gate.mulVec vector (((0,()),(0,())),u) = hadamardCoefficient^3 := by
  change (∑ p : ((Fin 2 × Unit) × (Fin 2 × Unit)) × Fin 2,
    gate (((0,()),(0,())),u) p * vector p) = _
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_unique]
  fin_cases u <;> norm_num [gate, basisGate, blockGate, bitGate, hadamard, vector,
    Op.tensor, Op.ident, Matrix.kronecker, Matrix.kroneckerMap, Matrix.one_apply] <;> ring

/-- Measuring the two signal registers retains Eve's off-diagonal entry
inside the actual zero/zero outcome. -/
theorem measured_coherence :
    ((FirstRegister.channel pairSpace .bit).run
      (((BB84ErrorTransform.basisChannel 1 (fun _ => .X)).amplify .bit).run state)).matrix
      (Fintype.equivFin pairSpace.Basis ((0,()),(0,())),0)
      (Fintype.equivFin pairSpace.Basis ((0,()),(0,())),1) = 1/8 := by
  change (FirstRegister.channel pairSpace .bit).toKraus.apply
    ((Kraus.single gate).apply (rank vector vector)) _ _ = _
  rw [FirstRegister.apply_entry, if_pos rfl, Kraus.single_apply,
    SourceReplacement.rank_conjugate]
  change gate.mulVec vector (((0,()),(0,())),0) *
    star (gate.mulVec vector (((0,()),(0,())),1)) = 1/8
  rw [amplitude, amplitude]
  norm_num [star_pow, starRingEnd_apply]
  calc
    hadamardCoefficient^3 * hadamardCoefficient^3 =
        (hadamardCoefficient * hadamardCoefficient)^3 := by ring
    _ = 1/8 := by rw [hadamardCoefficient_square]; norm_num

def bases (i : Fin 2) : Fin 1 → BB84Basis := fun _ => if i = 0 then .Z else .X

def channels : Nat → Channel (BB84CNOTLogic.recordSpace 1 .bit)
    (BB84CNOTLogic.recordSpace 1 .bit) := fun _ => dephase _

/-- The concrete entangled input validates the finite mixed-basis derivation
including measurement, classical relabelling and actual physical processing. -/
theorem interpreted :
    (BB84CNOTLogic.model state channels).Carrier
      (.processed 2 bases (Foundation.Probability.uniform (Fin 2)) 0) :=
  BB84CNOTLogic.sound state channels
    (BB84CNOTLogic.proof 2 bases (Foundation.Probability.uniform (Fin 2)) 0)
    (fun i => Fin.elim0 i)

def transformedGate : Op jointSpace jointSpace :=
  Op.tensor (basisGate 1 (fun _ => .X) * Op.basisMap (cnotEquiv 1)) (Op.ident .bit)

theorem transformed_amplitude (b u : Fin 2) :
    transformedGate.mulVec vector (((b,()),(0,())),u) = hadamardCoefficient^3 := by
  change (Op.tensor (Op.seq (Op.basisMap (cnotEquiv 1)) (basisGate 1 (fun _ => .X)))
    (Op.ident .bit)).mulVec vector _ = _
  rw [Op.basisMap_seq]
  change (∑ p : ((Fin 2 × Unit) × (Fin 2 × Unit)) × Fin 2,
    Op.tensor (fun i j => basisGate 1 (fun _ => .X) i (cnotEquiv 1 j)) (Op.ident .bit)
      (((b,()),(0,())),u) p * vector p) = _
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_unique]
  fin_cases b <;> fin_cases u <;>
    norm_num [basisGate, blockGate, bitGate, hadamard, vector, cnotEquiv, BB84ErrorTransform.xor, bitXor,
      Op.tensor, Op.ident, Matrix.kronecker, Matrix.kroneckerMap, Matrix.one_apply] <;> ring

theorem transformed_rank :
    ((original 1 (fun _ => .X)).amplify .bit).toKraus.apply state.matrix =
      rank (transformedGate.mulVec vector) (transformedGate.mulVec vector) := by
  simp only [original, cnotChannel, BB84ErrorTransform.basisChannel, BasisChannel.channel,
    Channel.seq, Channel.amplify, Channel.ofIsometry, Kraus.seq, Kraus.amplify,
    Kraus.apply, Kraus.single, Fintype.sum_prod_type, Fintype.sum_unique]
  exact SourceReplacement.rank_conjugate transformedGate vector

/-- Error-first measurement retains coherence between different key values
and different Eve values in the actual CNOT-transformed experiment. -/
theorem error_first_coherence :
    (BB84DelayedMeasurements.first (n := 1) (fun _ => .X) .bit).toKraus.apply
      (((original 1 (fun _ => .X)).amplify .bit).toKraus.apply state.matrix)
      (BB84DelayedMeasurements.errorLabel (n := 1) (fun _ => .X)
        ((((0,()),(0,())),0) : jointSpace.Basis),(((0,()),(0,())),0))
      (BB84DelayedMeasurements.errorLabel (n := 1) (fun _ => .X)
        ((((0,()),(0,())),0) : jointSpace.Basis),(((1,()),(0,())),1)) = 1/8 := by
  rw [BB84DelayedMeasurements.first_entry]
  · rw [transformed_rank]
    change transformedGate.mulVec vector (((0,()),(0,())),0) *
      star (transformedGate.mulVec vector (((1,()),(0,())),1)) = _
    rw [transformed_amplitude, transformed_amplitude]
    norm_num [star_pow, starRingEnd_apply]
    calc
      hadamardCoefficient^3 * hadamardCoefficient^3 =
          (hadamardCoefficient * hadamardCoefficient)^3 := by ring
      _ = 1/8 := by rw [hadamardCoefficient_square]; norm_num
  · rfl

/-- The same entangled input interprets the new measurement-order derivation. -/
theorem delayed_interpreted :
    (BB84CNOTLogic.model state channels).Carrier (.delayed (fun _ => .X)) :=
  BB84CNOTLogic.sound state channels (BB84CNOTLogic.delayedProof (fun _ => .X))
    (fun i => Fin.elim0 i)

/-- The actual public sample test accepts agreement and rejects disagreement. -/
theorem sample_decisions :
    RawProtocol.accepts (n := 1) (fun _ => .X) (fun _ => .X)
      (fun _ => 0) (fun _ => 0) Finset.univ 0 0 = true ∧
    RawProtocol.accepts (n := 1) (fun _ => .X) (fun _ => .X)
      (fun _ => 0) (fun _ => 1) Finset.univ 0 0 = false := by
  norm_num [RawProtocol.accepts, RawProtocol.keyPositions, RawProtocol.matched, RawProtocol.errors]

/-- The same public test rejects when too few untested key positions remain. -/
theorem length_abort :
    RawProtocol.accepts (n := 1) (fun _ => .X) (fun _ => .X)
      (fun _ => 0) (fun _ => 0) Finset.univ 1 0 = false := by
  norm_num [RawProtocol.accepts, RawProtocol.keyPositions, RawProtocol.matched, RawProtocol.errors]

/-- Accepted branch retains actual Eve coherence after recording the key.
The full sample here leaves no final key; this validates the branch channel. -/
theorem accepted_coherence :
    ((BB84DelayedDecision.before (n := 1) (fun _ => .X) .bit Finset.univ 0 0).branch 0).apply
      (((original 1 (fun _ => .X)).amplify .bit).toKraus.apply state.matrix)
      (BB84DelayedMeasurements.keyLabel (n := 1) (fun _ => .X)
        ((((0,()),(0,())),0) : jointSpace.Basis),
        (BB84DelayedMeasurements.errorLabel (n := 1) (fun _ => .X)
          ((((0,()),(0,())),0) : jointSpace.Basis),(((0,()),(0,())),0)))
      (BB84DelayedMeasurements.keyLabel (n := 1) (fun _ => .X)
        ((((0,()),(0,())),0) : jointSpace.Basis),
        (BB84DelayedMeasurements.errorLabel (n := 1) (fun _ => .X)
          ((((0,()),(0,())),0) : jointSpace.Basis),(((0,()),(0,())),1))) = 1/8 := by
  have ha : BB84DelayedDecision.accepts (Finset.univ : Finset (Fin 1)) 0 0
      (BB84DelayedMeasurements.errorLabel (n := 1) (fun _ => .X)
        ((((0,()),(0,())),0) : jointSpace.Basis)) := by
    have hz : errorBits (n := 1) (fun _ => .X) ((0,()),(0,())) = fun _ => 0 := by
      funext i; fin_cases i; rfl
    simp [BB84DelayedDecision.accepts, BB84DelayedMeasurements.errorLabel, hz]
  change ((PartitionMeasurement.decideBefore _ _ _).branch 0).apply _ _ _ = _
  rw [PartitionMeasurement.decision_entry]
  simp only [ite_true, ha, and_self]
  rw [if_pos ⟨trivial,trivial,rfl⟩, if_pos ⟨trivial,trivial,rfl⟩, transformed_rank]
  change transformedGate.mulVec vector (((0,()),(0,())),0) *
    star (transformedGate.mulVec vector (((0,()),(0,())),1)) = _
  rw [transformed_amplitude, transformed_amplitude]
  norm_num [star_pow, starRingEnd_apply]
  calc
    hadamardCoefficient^3 * hadamardCoefficient^3 =
        (hadamardCoefficient * hadamardCoefficient)^3 := by ring
    _ = 1/8 := by rw [hadamardCoefficient_square]; norm_num

/-- The public decision rule has a closed derivation on the entangled model. -/
theorem decision_interpreted :
    (BB84CNOTLogic.model state channels).Carrier
      (.decision (fun _ => .X) Finset.univ 0 0) :=
  BB84CNOTLogic.sound state channels
    (BB84CNOTLogic.decisionProof (fun _ => .X) Finset.univ 0 0) (fun i => Fin.elim0 i)

/-- A nonempty private raw key can be retained in the common-basis example.
This is a concrete classical-output check, not a security statement. -/
theorem raw_key_present :
    (RawProtocol.output (n := 1) (fun _ => .X) (fun _ => .X)
      (fun _ => 0) (fun _ => 0) ∅ 1 0).aliceKey 0 = some 0 ∧
    (RawProtocol.output (n := 1) (fun _ => .X) (fun _ => .X)
      (fun _ => 0) (fun _ => 0) ∅ 1 0).bobKey 0 = some 0 := by
  norm_num [RawProtocol.output, RawProtocol.accepts, RawProtocol.keyPositions,
    RawProtocol.matched, RawProtocol.errors]

/-- The entangled model interprets raw-output reconstruction with a retained
key position and no sample. No secrecy is asserted without a sample bound. -/
theorem raw_interpreted :
    (BB84CNOTLogic.model state channels).Carrier (.raw (fun _ => .X) ∅ 1 0) :=
  BB84CNOTLogic.sound state channels (BB84CNOTLogic.rawProof (fun _ => .X) ∅ 1 0)
    (fun i => Fin.elim0 i)

/-- The same model also interprets reconstruction when the length guard
forces abort and both private keys are erased by the existing raw format. -/
theorem raw_abort_interpreted :
    (BB84CNOTLogic.model state channels).Carrier (.raw (fun _ => .X) Finset.univ 1 0) :=
  BB84CNOTLogic.sound state channels (BB84CNOTLogic.rawProof (fun _ => .X) Finset.univ 1 0)
    (fun i => Fin.elim0 i)

/-- Early explicit decision, key measurement, discard and raw reconstruction
are interpreted together on the same entangled three-qubit model. -/
theorem decidedRaw_interpreted :
    (BB84CNOTLogic.model state channels).Carrier (.decidedRaw (fun _ => .X) ∅ 1 0) :=
  BB84CNOTLogic.sound state channels (BB84CNOTLogic.decidedRawProof (fun _ => .X) ∅ 1 0)
    (fun i => Fin.elim0 i)

/-- The complete channel also interprets the length-guard abort case. -/
theorem decidedRaw_abort_interpreted :
    (BB84CNOTLogic.model state channels).Carrier (.decidedRaw (fun _ => .X) Finset.univ 1 0) :=
  BB84CNOTLogic.sound state channels
    (BB84CNOTLogic.decidedRawProof (fun _ => .X) Finset.univ 1 0) (fun i => Fin.elim0 i)

/-- An actual computational-basis copying attack gives the prepared-output
interpretation and has nonzero Bob/Eve coherence on the X preparation. -/
theorem prepared_attack_interpreted :
    (BB84DecisionRaw.decided (n := 1) (fun _ => .X) .bit ∅ 1 0).toKraus.apply
        (BB84PreparedInput.input SourceReplacementExamples.attack).matrix =
      (BB84PreparedRaw.prepared SourceReplacementExamples.attack (fun _ => .X) ∅ 1 0).matrix ∧
    (SourceReplacementExamples.attack.jointState (fun _ => .X) (fun _ => 0)).matrix
      ((0,()),0) ((1,()),1) = 1/2 :=
  ⟨BB84PreparedRawInterpretation.interpreted _ _ _ _ _,
    SourceReplacementExamples.attacked_X_entry⟩

/-- The same actual attack and source also interpret the length-guard abort. -/
theorem prepared_attack_abort_interpreted :
    (BB84DecisionRaw.decided (n := 1) (fun _ => .X) .bit Finset.univ 1 0).toKraus.apply
        (BB84PreparedInput.input SourceReplacementExamples.attack).matrix =
      (BB84PreparedRaw.prepared SourceReplacementExamples.attack
        (fun _ => .X) Finset.univ 1 0).matrix :=
  BB84PreparedRawInterpretation.interpreted _ _ _ _ _

end
end Foundation.Quantum.QKD.ErrorTransformExamples
