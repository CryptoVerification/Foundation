import Foundation.Quantum.QKD.BB84MixedPreparedRaw
import Foundation.Quantum.QKD.BB84RandomSource

/-! The physical common entangled input implements the complete randomized
BB84 preparation experiment with independently selected basis strings.
Only the signal is discarded; both private keys and Eve remain in the record. -/
namespace Foundation.Quantum.QKD.BB84MixedRandomSource
noncomputable section
set_option backward.isDefEq.respectTransparency false

def record {n : Nat} {e : Space} (A : BlockAttack n e) (k minKey tolerance : Nat) :
    Density (BB84MixedPreparedRaw.recordSpace n e) :=
  Density.mixture (Foundation.Probability.uniform (BB84RandomSource.Bases n)) (fun b =>
    Density.mixture (Randomized.testDistribution b.seed k) (fun T =>
      (BB84MixedPreparedRaw.reference b.alice b.bob e T
        (Randomized.requiredLength b.seed k minKey) tolerance).run (BB84PreparedInput.input A)))

/-- The source-presentation interpretation is valid before averaging each
basis and sample choice, and therefore for the whole randomized experiment. -/
theorem source_interpreted {n : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) :
    (record A k minKey tolerance).matrix =
      ((discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).run
        (BB84RandomSource.record A k minKey tolerance)).matrix := by
  unfold record BB84RandomSource.record
  rw [Density.mixture_channel]
  apply Density.mixture_congr_matrix
  intro b
  rw [Density.mixture_channel]
  apply Density.mixture_congr_matrix
  intro T
  exact (BB84MixedPreparedRaw.source_interpreted A b.alice b.bob T
    (Randomized.requiredLength b.seed k minKey) tolerance).symm

/-- Includes the original insufficient-population abort guard and the actual
nonreplacement test law; no acceptance probability is divided out. -/
theorem record_eq {n : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) :
    (record A k minKey tolerance).matrix =
      ((discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).run
        (Randomized.record A k minKey tolerance)).matrix := by
  rw [source_interpreted]
  change (discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).toKraus.apply _ = _
  rw [BB84RandomSource.record_eq]
  rfl

/-- The resulting public transcript jointly with Eve is exactly the original
randomized public experiment, not merely the same classical marginal. -/
theorem public_eq {n : Nat} {e : Space} (A : BlockAttack n e)
    (k minKey tolerance : Nat) :
    ((BB84DeferredRaw.publicChannel n e).run (record A k minKey tolerance)).matrix =
      (Randomized.publicState A k minKey tolerance).matrix := by
  change (BB84DeferredRaw.publicChannel n e).toKraus.apply _ = _
  rw [record_eq]
  change (BB84DeferredRaw.publicChannel n e).toKraus.apply
    ((discardMiddle (.register (Fintype.card (RawProtocol.Output n))) (qubits n) e).toKraus.apply
      (Randomized.record A k minKey tolerance).matrix) = _
  rw [show (Randomized.publicState A k minKey tolerance).matrix =
    (RawProtocol.publicChannel n e).toKraus.apply (Randomized.record A k minKey tolerance).matrix from rfl,
    RawProtocol.publicChannel, Channel.seq, Kraus.seq_apply]
  exact (classicalMap_discardMiddle (qubits n) e _ _).symm

end
end Foundation.Quantum.QKD.BB84MixedRandomSource
