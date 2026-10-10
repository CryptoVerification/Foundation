import Foundation.Quantum.QKD.BB84PreparedInput
import Foundation.Quantum.BasisRecordDiscard
import Foundation.Quantum.InstrumentRecordPre
import Foundation.Quantum.ClassicalDiscard

/-! Connect the basis-independent entangled input and early-decision channel
to the actual existing uniformly weighted prepare/attack/raw-record experiment.
Bases and the public test set are fixed here; attacks may act on the whole block. -/
namespace Foundation.Quantum.QKD.BB84PreparedRaw
noncomputable section
open BB84ErrorTransform BB84DelayedMeasurements BB84OutcomeCoordinates BB84DeferredRaw BB84PreparedInput
set_option backward.isDefEq.respectTransparency false

abbrev recordSpace (n : Nat) (e : Space) :=
  Space.tensor (.register (Fintype.card (RawProtocol.Output n))) e

def prepared {n : Nat} {e : Space} (A : BlockAttack n e) (θ : Fin n → BB84Basis)
    (T : Finset (Fin n)) (minKey tolerance : Nat) : Density (recordSpace n e) :=
  Density.mixture (Foundation.Probability.uniform (qubits n).Basis) (fun a =>
    (discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).run
      (RawProtocol.record A θ θ (readBits a) T minKey tolerance))

/-- The existing prepare/attack/Bob-measurement record, with only Bob's
quantum output discarded, is an explicit first-register classical record. -/
theorem raw_record_discard {n : Nat} {e : Space} (A : BlockAttack n e)
    (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat) (a : (qubits n).Basis) :
    ((discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).run
      (RawProtocol.record A θ θ (readBits a) T minKey tolerance)).matrix =
    (classicalMap e (fun r => rawLabel θ T minKey tolerance
      ((Fintype.equivFin (qubits n).Basis).symm r,a))).toKraus.apply
        ((FirstRegister.channel (qubits n) e).toKraus.apply
          (((blockBasisChannel n θ).amplify e).toKraus.apply (A.jointState θ (readBits a)).matrix)) := by
  change (discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).toKraus.apply
    ((classicalMap (.tensor (qubits n) e) (fun r => Fintype.equivFin (RawProtocol.Output n)
      (RawProtocol.output θ θ (readBits a) (blockOutcomeBits n r) T minKey tolerance))).toKraus.apply
        (((blockMeasurement n θ).amplify e).record.toKraus.apply (A.jointState θ (readBits a)).matrix)) = _
  rw [classicalMap_discardMiddle]
  unfold blockMeasurement
  rw [Instrument.amplify_record_pre_apply, basis_record_discard]
  rfl

/-- The common-basis entangled experiment is exactly the actual uniform
prepare/attack experiment in the existing raw-output implementation. -/
theorem reference_prepared {n : Nat} {e : Space} (A : BlockAttack n e)
    (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat) :
    (reference θ e T minKey tolerance).toKraus.apply (input A).matrix =
      (prepared A θ T minKey tolerance).matrix := by
  change ((((BB84ErrorTransform.basisChannel n θ).amplify e).toKraus.seq
    (FirstRegister.channel (signalSpace n) e).toKraus).seq
      (classicalMap e (fun r => rawLabel θ T minKey tolerance
        ((Fintype.equivFin (signalSpace n).Basis).symm r))).toKraus).apply (input A).matrix = _
  simp only [Kraus.seq_apply]
  ext ⟨r,u⟩ ⟨s,v⟩
  rw [classicalMap_apply]
  let B (a : (qubits n).Basis) := (FirstRegister.channel (qubits n) e).toKraus.apply
    (((blockBasisChannel n θ).amplify e).toKraus.apply (A.jointState θ (readBits a)).matrix)
  have hp (a : (qubits n).Basis) :
      ((discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).run
        (RawProtocol.record A θ θ (readBits a) T minKey tolerance)).matrix (r,u) (s,v) =
      if r = s then ∑ t, if rawLabel θ T minKey tolerance
        ((Fintype.equivFin (qubits n).Basis).symm t,a) = r then B a (t,u) (t,v) else 0 else 0 := by
    rw [raw_record_discard, classicalMap_apply]
  have hm (t : Fin (Fintype.card (signalSpace n).Basis)) :
      (FirstRegister.channel (signalSpace n) e).toKraus.apply
        (((BB84ErrorTransform.basisChannel n θ).amplify e).toKraus.apply (input A).matrix) (t,u) (t,v) =
      (1/2:ℂ)^n * B ((Fintype.equivFin (signalSpace n).Basis).symm t).2
        (Fintype.equivFin (qubits n).Basis ((Fintype.equivFin (signalSpace n).Basis).symm t).1,u)
        (Fintype.equivFin (qubits n).Basis ((Fintype.equivFin (signalSpace n).Basis).symm t).1,v) := by
    simpa only [Equiv.apply_symm_apply, ite_true] using measured_block A θ
      ((Fintype.equivFin (signalSpace n).Basis).symm t)
      ((Fintype.equivFin (signalSpace n).Basis).symm t) u v
  simp_rw [hm]
  simp only [prepared, Density.mixture, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [hp, BB84Source.uniform_weight]
  by_cases h : r = s
  · subst s
    simp only [ite_true]
    change (∑ t, (if rawLabel θ T minKey tolerance ((Fintype.equivFin (signalSpace n).Basis).symm t) = r then
      (1/2:ℂ)^n * B ((Fintype.equivFin (signalSpace n).Basis).symm t).2
        (Fintype.equivFin (qubits n).Basis ((Fintype.equivFin (signalSpace n).Basis).symm t).1,u)
        (Fintype.equivFin (qubits n).Basis ((Fintype.equivFin (signalSpace n).Basis).symm t).1,v) else 0)) =
      ∑ a, (1/2:ℂ)^n * ∑ t, if rawLabel θ T minKey tolerance
        ((Fintype.equivFin (qubits n).Basis).symm t,a) = r then B a (t,u) (t,v) else 0
    rw [Equiv.sum_comp (Fintype.equivFin (signalSpace n).Basis).symm
      (fun p => if rawLabel θ T minKey tolerance p = r then
        (1/2:ℂ)^n * B p.2 (Fintype.equivFin (qubits n).Basis p.1,u)
          (Fintype.equivFin (qubits n).Basis p.1,v) else 0)]
    change (∑ p : (qubits n).Basis × (qubits n).Basis, _) = _
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    have hb := Equiv.sum_comp (Fintype.equivFin (qubits n).Basis).symm
      (fun b => if rawLabel θ T minKey tolerance (b,a) = r then
        B a (Fintype.equivFin (qubits n).Basis b,u) (Fintype.equivFin (qubits n).Basis b,v) else 0)
    simp only [Equiv.apply_symm_apply] at hb
    rw [hb, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hc : rawLabel θ T minKey tolerance (b,a) = r <;> simp [hc]
  · simp only [h, ite_false, mul_zero, Finset.sum_const_zero]

theorem decided_prepared {n : Nat} {e : Space} (A : BlockAttack n e)
    (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat) :
    (BB84DecisionRaw.decided θ e T minKey tolerance).toKraus.apply (input A).matrix =
      (prepared A θ T minKey tolerance).matrix :=
  (BB84DecisionRaw.output_eq θ T minKey tolerance (input A).matrix).trans
    (reference_prepared A θ T minKey tolerance)

/-- Forgetting the private keys gives the actual existing public experiment,
averaged over Alice's uniform preparations. Eve is retained, not measured. -/
theorem public_prepared {n : Nat} {e : Space} (A : BlockAttack n e)
    (θ : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat) :
    ((BB84DeferredRaw.publicChannel n e).run (prepared A θ T minKey tolerance)).matrix =
      (Density.mixture (Foundation.Probability.uniform (qubits n).Basis) (fun a =>
        RawProtocol.publicState A θ θ (readBits a) T minKey tolerance)).matrix := by
  unfold prepared
  rw [Density.mixture_channel]
  change (∑ a, _ • _) = ∑ a, _ • _
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  change (BB84DeferredRaw.publicChannel n e).toKraus.apply
    ((discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).toKraus.apply
      (RawProtocol.record A θ θ (readBits a) T minKey tolerance).matrix) =
    (RawProtocol.publicChannel n e).toKraus.apply
      (RawProtocol.record A θ θ (readBits a) T minKey tolerance).matrix
  rw [RawProtocol.publicChannel, Channel.seq, Kraus.seq_apply]
  exact (classicalMap_discardMiddle (qubits n) e _ _).symm


end
end Foundation.Quantum.QKD.BB84PreparedRaw
