import Foundation.Quantum.ClassicalControl
import Foundation.Quantum.QKD.SourceReplacementLogic
import Foundation.Quantum.QKD.BB84Randomized

/-! Source replacement through Bob's physical measurement and the existing
raw-key output, for fixed bases and a specified test set. The full public
record, abort decision, both private keys, Bob and Eve are retained. -/
namespace Foundation.Quantum.QKD.BB84RawSource
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev outputSpace (n : Nat) (e : Space) :=
  Space.tensor (.register (Fintype.card (RawProtocol.Output n))) (.tensor (qubits n) e)

def selected {n : Nat} (e : Space) (alice bob : Fin n → BB84Basis)
    (T : Finset (Fin n)) (minKey tolerance : Nat)
    (x : Fin (Fintype.card (qubits n).Basis)) :
    Channel (.tensor (qubits n) e) (outputSpace n e) :=
  ((blockMeasurement n bob).amplify e).record |>.seq
    (classicalMap (.tensor (qubits n) e) (fun r => Fintype.equivFin (RawProtocol.Output n)
      (RawProtocol.output alice bob (blockOutcomeBits n x) (blockOutcomeBits n r)
        T minKey tolerance)))

def channel {n : Nat} (e : Space) (alice bob : Fin n → BB84Basis)
    (T : Finset (Fin n)) (minKey tolerance : Nat) :
    Channel (SourceReplacementLogic.recordSpace n e) (outputSpace n e) :=
  ClassicalControl.channel (selected e alice bob T minKey tolerance)

def state {n : Nat} {e : Space} (A : BlockAttack n e) (alice bob : Fin n → BB84Basis)
    (T : Finset (Fin n)) (minKey tolerance : Nat) : Density (outputSpace n e) :=
  (channel e alice bob T minKey tolerance).run (BB84Source.record A alice)

theorem selected_record {n : Nat} {e : Space} (A : BlockAttack n e)
    (alice bob : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat)
    (x : (qubits n).Basis) :
    ((selected e alice bob T minKey tolerance (Fintype.equivFin (qubits n).Basis x)).run
      (A.jointState alice (readBits x))).matrix =
      (RawProtocol.record A alice bob (readBits x) T minKey tolerance).matrix := by
  rw [selected, Channel.seq_run_matrix]
  simp only [blockOutcomeBits, Equiv.symm_apply_apply]
  rfl

/-- Applying the actual controlled measurement to the ordinary preparation
ensemble gives the existing raw output, averaged over uniform private bits. -/
theorem prepared {n : Nat} {e : Space} (A : BlockAttack n e)
    (alice bob : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat) :
    ((channel e alice bob T minKey tolerance).run (BB84Source.ensemble A alice)).matrix =
      (Density.mixture (Foundation.Probability.uniform (qubits n).Basis) (fun x =>
        RawProtocol.record A alice bob (readBits x) T minKey tolerance)).matrix := by
  rw [BB84Source.ensemble, Density.mixture_channel]
  change (∑ x, _ • _) = ∑ x, _ • _
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  rw [show ((channel e alice bob T minKey tolerance).run _).matrix =
    ((ClassicalControl.channel (selected e alice bob T minKey tolerance)).run _).matrix from rfl,
    ClassicalControl.basis, selected_record]

/-- The source equality is obtained from a closed finite derivation in the
existing presentation, then transported through the real raw-output channel. -/
theorem interpreted {n : Nat} {e : Space} (A : BlockAttack n e)
    (alice bob : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat) :
    (state A alice bob T minKey tolerance).matrix =
      (Density.mixture (Foundation.Probability.uniform (qubits n).Basis) (fun x =>
        RawProtocol.record A alice bob (readBits x) T minKey tolerance)).matrix := by
  let d : Foundation.Logic.Derivation SourceReplacementLogic.presentation (.empty _)
      (.entangled 0, .prepared 0) := .apply (T := SourceReplacementLogic.presentation) (.source 0) (fun i => Fin.elim0 i)
  have h := SourceReplacementLogic.sound A (fun _ => alice)
    (fun _ => Channel.identity _) d (fun i => Fin.elim0 i)
  change (BB84Source.record A alice).matrix = (BB84Source.ensemble A alice).matrix at h
  change (channel e alice bob T minKey tolerance).toKraus.apply _ = _
  rw [h]
  exact prepared A alice bob T minKey tolerance

/-- The existing guard for insufficient matched positions is retained. Only
the private input string is averaged; bases and test positions stay fixed. -/
theorem configuration {n : Nat} {e : Space} (A : BlockAttack n e)
    (c : Randomized.Configuration n) (k minKey tolerance : Nat) :
    (state A c.seed.alice c.seed.bob c.tested
      (Randomized.requiredLength c.seed k minKey) tolerance).matrix =
      (Density.mixture (Foundation.Probability.uniform (qubits n).Basis) (fun x =>
        Randomized.conditionalRecord A
          ⟨⟨c.seed.alice, c.seed.bob, readBits x⟩, c.tested⟩ k minKey tolerance)).matrix := by
  exact interpreted A c.seed.alice c.seed.bob c.tested
    (Randomized.requiredLength c.seed k minKey) tolerance

/-- The actual public interface discards the private keys and Bob's quantum
output, and retains the transcript jointly with Eve. -/
theorem public_record {n : Nat} {e : Space} (A : BlockAttack n e)
    (alice bob : Fin n → BB84Basis) (T : Finset (Fin n)) (minKey tolerance : Nat) :
    ((RawProtocol.publicChannel n e).run
      (state A alice bob T minKey tolerance)).matrix =
      (Density.mixture (Foundation.Probability.uniform (qubits n).Basis) (fun x =>
        RawProtocol.publicState A alice bob (readBits x) T minKey tolerance)).matrix := by
  change (RawProtocol.publicChannel n e).toKraus.apply _ = _
  rw [interpreted]
  exact Density.mixture_channel _ _ _

end
end Foundation.Quantum.QKD.BB84RawSource
