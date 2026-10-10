import Foundation.Quantum.QKD.PairwiseAlicePrivacy
import Foundation.Quantum.QKD.PairwiseAlicePhysical
import Foundation.Quantum.QKD.SplitLeak

/-! Actual test-position disclosure and removal from Alice's private key.
The coefficient costs exactly 2^(number of tested positions), as in the
chain step of Bouman--Fehr §6 p.21. Error correction is not instantiated here. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open PureProjection
set_option backward.isDefEq.respectTransparency false

def testEquiv {n : Nat} (T : Finset (Fin n)) : (qubits n).Basis ≃
    ((qubits (BB84SiftedInput.remainderCount T)).Basis ×
      (qubits (BB84SiftedInput.selectedCount T)).Basis) :=
  (BB84SiftedInput.splitEquiv T).trans (Equiv.prodComm _ _)

theorem test_bits {n : Nat} (T : Finset (Fin n)) (x : (qubits n).Basis)
    (i : Fin (BB84SiftedInput.selectedCount T)) :
    readBits (testEquiv T x).2 i = readBits x (BB84SiftedInput.selectedIndex T i).val := by
  simp only [testEquiv, Equiv.trans_apply, Equiv.prodComm_apply,
    BB84SiftedInput.splitEquiv, Equiv.coe_fn_mk, BB84SiftedInput.split, Prod.swap, read_write]

theorem remaining_bits {n : Nat} (T : Finset (Fin n)) (x : (qubits n).Basis)
    (i : Fin (BB84SiftedInput.remainderCount T)) :
    readBits (testEquiv T x).1 i = readBits x (BB84SiftedInput.remainderIndex T i).val := by
  simp only [testEquiv, Equiv.trans_apply, Equiv.prodComm_apply,
    BB84SiftedInput.splitEquiv, Equiv.coe_fn_mk, BB84SiftedInput.split, Prod.swap, read_write]

def testedKey {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) :=
  Subnormalized.withPublic
    (Subnormalized.relabel (acceptedAlice v hv k gap minKey tolerance c) (testEquiv c.2))

theorem tested_alphabet {n : Nat} (T : Finset (Fin n)) :
    Fintype.card (qubits (BB84SiftedInput.selectedCount T)).Basis = 2^T.card := by
  rw [Fintype.card_congr (bitStringEquiv _)]
  simp only [Fintype.card_fun, Fintype.card_fin, BB84SiftedInput.selectedCount, Fintype.card_coe]

theorem tested_dominated {n : Nat} {e : Space}
    (v : (BB84DelayedMeasurements.jointSpace n e).Basis → ℂ) (hv : bracket v v = 1)
    (k gap minKey tolerance : Nat) (c : PairwiseSampling.Configuration n) :
    Subnormalized.Dominated (testedKey v hv k gap minKey tolerance c)
      (Subnormalized.leakedReference (C := (qubits (BB84SiftedInput.selectedCount c.2)).Basis)
        (reference v hv k gap c)) ((2:ℝ)^c.2.card * bound k gap minKey tolerance c) := by
  have h := Subnormalized.split_dominated (acceptedAlice v hv k gap minKey tolerance c)
    (testEquiv c.2) (reference v hv k gap c) (bound k gap minKey tolerance c)
    (acceptedAlice_dominated v hv k gap minKey tolerance c)
  simpa only [tested_alphabet, Nat.cast_pow, Nat.cast_ofNat, testedKey] using h

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
