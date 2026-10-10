import Foundation.Quantum.QKD.BB84SiftedRandomExperiment
import Foundation.Quantum.QKD.BB84MixedRandomSource
import Foundation.Quantum.FirstRegisterTransport
import Foundation.Quantum.QKD.SourceReplacementExamples

/-! Actual nontrivial copying attack in the sifting constructions.
These are validation examples, not a finite-key secrecy claim. -/
namespace Foundation.Quantum.QKD.SiftingExamples
noncomputable section
open BB84SiftedInput PureProjection
set_option backward.isDefEq.respectTransparency false

theorem counts :
    selectedCount (Finset.univ : Finset (Fin 1)) = 1 ∧
      remainderCount (Finset.univ : Finset (Fin 1)) = 0 := by
  simp [selectedCount, remainderCount]

/-- The actual attacked entangled source has a nonzero joint coherence. -/
theorem source_input_coherence :
    (BB84PreparedInput.input SourceReplacementExamples.attack).matrix
      (((0,()),(0,())),0) (((1,()),(1,())),1) = 1/2 := by
  change (BasisChannel.channel (TensorExchange.equivalence (qubits 1) .bit (qubits 1))).toKraus.apply
    ((Kraus.single (Op.tensor SourceReplacementExamples.dilation (Op.ident (qubits 1)))).apply
      (BB84Source.entangled 1).matrix) _ _ = _
  rw [BasisChannel.apply]
  change (Kraus.single (Op.tensor SourceReplacementExamples.dilation (Op.ident (qubits 1)))).apply
    (rank (SourceReplacement.pairVector (qubits 1) (hadamardCoefficient^1))
      (SourceReplacement.pairVector (qubits 1) (hadamardCoefficient^1)))
      (((0,()),0),(0,())) (((1,()),1),(1,())) = _
  rw [Kraus.single_apply, SourceReplacement.rank_conjugate]
  simp only [rank, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.mulVec, dotProduct]
  change (∑ p : (Fin 2 × Unit) × (Fin 2 × Unit),
      Op.tensor SourceReplacementExamples.dilation (Op.ident (qubits 1)) (((0,()),0),(0,())) p *
        SourceReplacement.pairVector (qubits 1) (hadamardCoefficient^1) p) *
    star (∑ p : (Fin 2 × Unit) × (Fin 2 × Unit),
      Op.tensor SourceReplacementExamples.dilation (Op.ident (qubits 1)) (((1,()),1),(1,())) p *
        SourceReplacement.pairVector (qubits 1) (hadamardCoefficient^1) p) = _
  simp only [Op.tensor, Matrix.kronecker, Matrix.kroneckerMap, Op.ident, Matrix.one_apply,
    SourceReplacementExamples.dilation, SourceReplacement.pairVector, pow_one]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_unique]
  dsimp only [Matrix.of_apply]
  have h01 : ((0,()) : (qubits 1).Basis) ≠ (1,()) := by
    intro h
    have hf : (0 : Fin 2) = 1 := congrArg Prod.fst h
    exact (by decide : (0 : Fin 2) ≠ 1) hf
  have h10 := Ne.symm h01
  simp only [h01, h10, ite_false]
  norm_num [starRingEnd_apply, hadamardCoefficient_square]

/-- Reversible selection preserves the same genuine cross-system coherence. -/
theorem selected_coherence (M : Finset (Fin 1)) :
    (input SourceReplacementExamples.attack M).matrix
      (jointEquiv M .bit ((((0,()),(0,())),0)))
      (jointEquiv M .bit ((((1,()),(1,())),1))) = 1/2 := by
  rw [input_entry]
  simp only [Equiv.symm_apply_apply]
  exact source_input_coherence

theorem selected_interpreted :
    (BB84CNOTLogic.model (input SourceReplacementExamples.attack Finset.univ)
      (fun _ => Channel.identity
        (BB84CNOTLogic.recordSpace (selectedCount (Finset.univ : Finset (Fin 1)))
          (auxiliary (Finset.univ : Finset (Fin 1)) .bit)))).Carrier
      (.decidedRaw (bases Finset.univ (fun _ => .X)) ∅ 1 0) :=
  interpreted _ _ _ _ _ _

/-- All independent bases and their actual test/abort distribution are kept. -/
theorem randomized_public_interpreted :
    ((RawProtocol.publicChannel 1 .bit).run
      (BB84SiftingRandomness.record SourceReplacementExamples.attack 1 1 0)).matrix =
      (Randomized.publicState SourceReplacementExamples.attack 1 1 0).matrix :=
  BB84SiftingRandomness.publicState_eq _ _ _ _

/-- The full actual public experiment also tolerates sampling directly in
selected-position numbers, including insufficient-population aborts. -/
theorem reindexed_public_interpreted :
    ((RawProtocol.publicChannel 1 .bit).run
      (reindexedRecord SourceReplacementExamples.attack 1 1 0)).matrix =
      (Randomized.publicState SourceReplacementExamples.attack 1 1 0).matrix :=
  reindexed_public_eq _ _ _ _

/-- Restore the selected raw output of the same actual attacked source after
interpreting the existing closed error-first derivation. -/
theorem restored_attack_interpreted :
    (restoreChannel (Finset.univ : Finset (Fin 1)) (fun _ => .X) (auxiliary Finset.univ .bit)).toKraus.apply
      ((BB84DecisionRaw.decided (bases Finset.univ (fun _ => .X)) (auxiliary Finset.univ .bit) ∅ 1 0).toKraus.apply
        (input SourceReplacementExamples.attack Finset.univ).matrix) =
    (restoreChannel (Finset.univ : Finset (Fin 1)) (fun _ => .X) (auxiliary Finset.univ .bit)).toKraus.apply
      ((BB84DeferredRaw.reference (bases Finset.univ (fun _ => .X)) (auxiliary Finset.univ .bit) ∅ 1 0).toKraus.apply
        (input SourceReplacementExamples.attack Finset.univ).matrix) :=
  restored_interpreted _ _ _ _ _ _

/-- A genuine error in one tested matched position causes abort in both
numberings, even if the other original position has a different basis. -/
theorem reindexed_error_abort :
    let M : Finset (Fin 2) := {0}
    RawProtocol.accepts (fun _ => .Z) (BB84SiftingRandomness.bobBases (fun _ => .Z) M)
      (fun _ => 0) (fun _ => 1) M 0 0 = false ∧
    RawProtocol.accepts (bases M (fun _ => .Z)) (bases M (fun _ => .Z))
      (bits M (fun _ => 0)) (bits M (fun _ => 1)) (restrictTest M M) 0 0 = false := by
  dsimp only
  have h : RawProtocol.accepts (fun _ => .Z)
      (BB84SiftingRandomness.bobBases (fun _ => .Z) ({0} : Finset (Fin 2)))
      (fun _ => 0) (fun _ => 1) {0} 0 0 = false := by
    norm_num [RawProtocol.accepts, RawProtocol.keyPositions, RawProtocol.errors,
      BB84SiftingRandomness.matched_bob]
  exact ⟨h, (accepts_eq {0} {0} (Finset.Subset.refl _) _ _ _ _ _).symm.trans h⟩

/-- Restore original-position raw labels, discard unmatched quantum signals,
and retain Eve in the same actual attack used above. -/
theorem discarded_attack_interpreted :
    (delayedOutput (Finset.univ : Finset (Fin 1)) (fun _ => .X) .bit ∅ 1 0).toKraus.apply
        (input SourceReplacementExamples.attack Finset.univ).matrix =
      (referenceOutput (Finset.univ : Finset (Fin 1)) (fun _ => .X) .bit ∅ 1 0).toKraus.apply
        (input SourceReplacementExamples.attack Finset.univ).matrix :=
  finished_interpreted _ _ _ _ _ _

/-- With no matched signals, the concrete different Bob/Alice bases operate
on the unmatched quantum block and disappear only after physical discard. -/
theorem unmatched_attack_irrelevant :
    (referenceOutput (∅ : Finset (Fin 1)) (fun _ => .X) .bit ∅ 1 0).toKraus.apply
      ((Kraus.single (Op.tensor (Op.ident (signalSpace (selectedCount (∅ : Finset (Fin 1)))))
        (Op.tensor (unmatchedGate (∅ : Finset (Fin 1)) (fun _ => .X)) (Op.ident .bit)))).apply
          (input SourceReplacementExamples.attack ∅).matrix) =
    (referenceOutput (∅ : Finset (Fin 1)) (fun _ => .X) .bit ∅ 1 0).toKraus.apply
      (input SourceReplacementExamples.attack ∅).matrix :=
  unmatched_basis_irrelevant _ _ _ _ _ _

/-- Actual coherent copying attack, with mismatched Alice X and Bob Z bases.
The equality retains every raw output and Eve's full conditional state. -/
theorem mixed_attack_interpreted :
    ((discardMiddle (.register (Fintype.card (RawProtocol.Output 1))) (qubits 1) .bit).run
      (BB84RawSource.state SourceReplacementExamples.attack (fun _ => .X) (fun _ => .Z) ∅ 1 0)).matrix =
      (BB84MixedPreparedRaw.reference (fun _ => .X) (fun _ => .Z) .bit ∅ 1 0).toKraus.apply
        (BB84PreparedInput.input SourceReplacementExamples.attack).matrix :=
  BB84MixedPreparedRaw.source_interpreted _ _ _ _ _ _

/-- The same nontrivial attack in the entire independent-basis randomized
experiment. The one-signal example is a semantic check, not a secure key. -/
theorem mixed_randomized_interpreted :
    (BB84MixedRandomSource.record SourceReplacementExamples.attack 0 1 0).matrix =
      ((discardMiddle (.register (Fintype.card (RawProtocol.Output 1))) (qubits 1) .bit).run
        (Randomized.record SourceReplacementExamples.attack 0 1 0)).matrix :=
  BB84MixedRandomSource.record_eq _ _ _ _

theorem mixed_public_interpreted :
    ((BB84DeferredRaw.publicChannel 1 .bit).run
      (BB84MixedRandomSource.record SourceReplacementExamples.attack 0 1 0)).matrix =
      (Randomized.publicState SourceReplacementExamples.attack 0 1 0).matrix :=
  BB84MixedRandomSource.public_eq _ _ _ _

/-- Full X/X selected delayed experiment equals the actual preparation
experiment for the coherent copying attack, including raw keys and Eve. -/
theorem delayed_attack_prepared :
    (delayedOutput (Finset.univ : Finset (Fin 1)) (fun _ => .X) .bit ∅ 1 0).toKraus.apply
      (input SourceReplacementExamples.attack Finset.univ).matrix =
      (BB84MixedPreparedRaw.prepared SourceReplacementExamples.attack (fun _ => .X)
        (BB84SiftingRandomness.bobBases (fun _ => .X) Finset.univ)
          (liftTest Finset.univ ∅) 1 0).matrix :=
  delayed_prepared _ _ _ _ _ _

/-- The no-matched-position X/Z branch has the actual source output, including
its abort record, after unmatched signals are physically discarded. -/
theorem delayed_unmatched_source :
    (delayedOutput (∅ : Finset (Fin 1)) (fun _ => .X) .bit ∅ 1 0).toKraus.apply
      (input SourceReplacementExamples.attack ∅).matrix =
      ((discardMiddle (.register (Fintype.card (RawProtocol.Output 1))) (qubits 1) .bit).run
        (BB84RawSource.state SourceReplacementExamples.attack (fun _ => .X)
          (BB84SiftingRandomness.bobBases (fun _ => .X) ∅) (liftTest ∅ ∅) 1 0)).matrix :=
  delayed_source _ _ _ _ _ _

theorem delayed_randomized_public :
    ((BB84DeferredRaw.publicChannel 1 .bit).run
      (delayedRecord SourceReplacementExamples.attack 0 1 0)).matrix =
      (Randomized.publicState SourceReplacementExamples.attack 0 1 0).matrix :=
  delayed_public_eq _ _ _ _

end
end Foundation.Quantum.QKD.SiftingExamples
