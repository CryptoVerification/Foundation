import Foundation.Quantum.QKD.BB84ErrorTransform
import Foundation.Quantum.BasisChannel
import Foundation.Quantum.FirstRegister

/-! Physical CNOT experiment equality, retaining arbitrary quantum side
information. No product-state or independent-attack assumption is made. -/
namespace Foundation.Quantum.QKD.BB84ErrorTransform
noncomputable section
set_option backward.isDefEq.respectTransparency false

def cnotChannel (n : Nat) : Channel (.tensor (qubits n) (qubits n)) (.tensor (qubits n) (qubits n)) :=
  BasisChannel.channel (cnotEquiv n)

def relabelChannel (n : Nat) (θ : Fin n → BB84Basis) :
    Channel (.tensor (qubits n) (qubits n)) (.tensor (qubits n) (qubits n)) :=
  BasisChannel.channel (relabelEquiv n θ)

def basisChannel (n : Nat) (θ : Fin n → BB84Basis) :
    Channel (.tensor (qubits n) (qubits n)) (.tensor (qubits n) (qubits n)) :=
  Channel.ofIsometry (basisGate n θ)
    (tensor_isometry _ _ (blockGate_isometry n θ) (blockGate_isometry n θ))

def original (n : Nat) (θ : Fin n → BB84Basis) := (cnotChannel n).seq (basisChannel n θ)
def modified (n : Nat) (θ : Fin n → BB84Basis) := (basisChannel n θ).seq (relabelChannel n θ)

theorem amplified (n : Nat) (θ : Fin n → BB84Basis) (e : Space)
    (ρ : Operator (.tensor (.tensor (qubits n) (qubits n)) e)) :
    ((original n θ).amplify e).toKraus.apply ρ = ((modified n θ).amplify e).toKraus.apply ρ := by
  simp only [original, modified, cnotChannel, relabelChannel, basisChannel, BasisChannel.channel,
    Channel.seq, Channel.amplify, Channel.ofIsometry, Kraus.seq, Kraus.amplify,
    Kraus.apply, Kraus.single, Fintype.sum_prod_type, Fintype.sum_unique]
  rw [operation]

def recordedOriginal {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (ρ : Density (.tensor (.tensor (qubits n) (qubits n)) e)) :
    Density (.tensor (.register (Fintype.card (Space.tensor (qubits n) (qubits n)).Basis)) e) :=
  (FirstRegister.channel (.tensor (qubits n) (qubits n)) e).run (((original n θ).amplify e).run ρ)

def recordedModified {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (ρ : Density (.tensor (.tensor (qubits n) (qubits n)) e)) :
    Density (.tensor (.register (Fintype.card (Space.tensor (qubits n) (qubits n)).Basis)) e) :=
  (classicalMap e (fun r => Fintype.equivFin (Space.tensor (qubits n) (qubits n)).Basis
    (relabelEquiv n θ ((Fintype.equivFin (Space.tensor (qubits n) (qubits n)).Basis).symm r)))).run
      ((FirstRegister.channel (.tensor (qubits n) (qubits n)) e).run (((basisChannel n θ).amplify e).run ρ))

/-- A CNOT before measurement is exactly the verified classical relabelling
after the original common-basis measurement, including every Eve coherence. -/
theorem recorded_of_amplified {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (ρ : Density (.tensor (.tensor (qubits n) (qubits n)) e))
    (h : ((original n θ).amplify e).toKraus.apply ρ.matrix =
      ((modified n θ).amplify e).toKraus.apply ρ.matrix) :
    (recordedOriginal θ ρ).matrix = (recordedModified θ ρ).matrix := by
  change (FirstRegister.channel (.tensor (qubits n) (qubits n)) e).toKraus.apply
    (((original n θ).amplify e).toKraus.apply ρ.matrix) = _
  rw [h]
  change (FirstRegister.channel (.tensor (qubits n) (qubits n)) e).toKraus.apply
    (((basisChannel n θ).toKraus.seq (relabelChannel n θ).toKraus).amplify e |>.apply ρ.matrix) = _
  rw [Kraus.amplify_seq, Kraus.seq_apply]
  exact FirstRegister.relabel _ _ (relabelEquiv n θ) _

theorem recorded_eq {n : Nat} (θ : Fin n → BB84Basis) {e : Space}
    (ρ : Density (.tensor (.tensor (qubits n) (qubits n)) e)) :
    (recordedOriginal θ ρ).matrix = (recordedModified θ ρ).matrix :=
  recorded_of_amplified θ ρ (amplified n θ e ρ.matrix)

end
end Foundation.Quantum.QKD.BB84ErrorTransform
