import Foundation.Quantum.QKD.BB84DelayedDecision

/-! The error/key labels determine the original signal outcomes reversibly.
These are classical transformations, not cloning operations on an unknown
quantum input. The ordering of the signal pair is Bob, Alice. -/
namespace Foundation.Quantum.QKD.BB84OutcomeCoordinates
noncomputable section
open BB84ErrorTransform BB84DelayedMeasurements
set_option backward.isDefEq.respectTransparency false

abbrev signalSpace (n : Nat) := Space.tensor (qubits n) (qubits n)

def decode {n : Nat} (θ : Fin n → BB84Basis) (p : Fin (count n) × Fin (count n)) :
    (signalSpace n).Basis :=
  (writeBits n (fun i => if θ i = .Z then (Fintype.equivFin (Fin n → Fin 2)).symm p.1 i
      else (Fintype.equivFin (Fin n → Fin 2)).symm p.2 i),
   writeBits n (fun i => if θ i = .Z then (Fintype.equivFin (Fin n → Fin 2)).symm p.2 i
      else (Fintype.equivFin (Fin n → Fin 2)).symm p.1 i))

def encode {n : Nat} (θ : Fin n → BB84Basis) (p : (signalSpace n).Basis) :
    Fin (count n) × Fin (count n) :=
  (Fintype.equivFin (Fin n → Fin 2) (errorBits θ p),
   Fintype.equivFin (Fin n → Fin 2) (keyBits θ p))

theorem decode_encode {n : Nat} (θ : Fin n → BB84Basis) (p : (signalSpace n).Basis) :
    decode θ (encode θ p) = p := by
  apply Prod.ext
  · change writeBits n _ = p.1
    rw [← write_read n p.1]
    congr 1
    funext i
    cases h : θ i <;> simp [encode, errorBits, keyBits, h]
  · change writeBits n _ = p.2
    rw [← write_read n p.2]
    congr 1
    funext i
    cases h : θ i <;> simp [encode, errorBits, keyBits, h]

theorem encode_decode {n : Nat} (θ : Fin n → BB84Basis) (p : Fin (count n) × Fin (count n)) :
    encode θ (decode θ p) = p := by
  apply Prod.ext
  · change Fintype.equivFin (Fin n → Fin 2) _ = p.1
    apply (Fintype.equivFin (Fin n → Fin 2)).symm.injective
    simp only [Equiv.symm_apply_apply]
    funext i
    simp only [errorBits, decode, read_write]
    cases θ i <;> simp
  · change Fintype.equivFin (Fin n → Fin 2) _ = p.2
    apply (Fintype.equivFin (Fin n → Fin 2)).symm.injective
    simp only [Equiv.symm_apply_apply]
    funext i
    simp only [keyBits, decode, read_write]
    cases θ i <;> simp

def equivalence {n : Nat} (θ : Fin n → BB84Basis) :
    (signalSpace n).Basis ≃ Fin (count n) × Fin (count n) where
  toFun := encode θ
  invFun := decode θ
  left_inv := decode_encode θ
  right_inv := encode_decode θ

/-- Invert both the error/key assignment and the CNOT relabelling. -/
def originalOutcomes {n : Nat} (θ : Fin n → BB84Basis) (p : Fin (count n) × Fin (count n)) :
    (signalSpace n).Basis := relabel n θ (decode θ p)

theorem originalOutcomes_encode {n : Nat} (θ : Fin n → BB84Basis) (p : (signalSpace n).Basis) :
    originalOutcomes θ (encode θ (relabel n θ p)) = p := by
  rw [originalOutcomes, decode_encode, relabel_involution]

end
end Foundation.Quantum.QKD.BB84OutcomeCoordinates
