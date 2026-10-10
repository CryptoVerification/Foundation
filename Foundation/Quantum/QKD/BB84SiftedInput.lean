import Foundation.Quantum.QKD.BB84PreparedInput
import Foundation.Quantum.QKD.BB84CNOTLogic
import Foundation.Quantum.QKD.BB84SiftingRandomness

/-! Reversible quantum selection of matched positions. Unmatched signals
are retained with the adversary as auxiliary information; arbitrary cross
position coherence is preserved. The input precedes all basis/test choices.
The full raw-record connection is proved in BB84SiftedFullRecord and
BB84SiftedRandomExperiment. -/
namespace Foundation.Quantum.QKD.BB84SiftedInput
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev selectedCount {n : Nat} (M : Finset (Fin n)) := Fintype.card {i // i ∈ M}
abbrev remainderCount {n : Nat} (M : Finset (Fin n)) := Fintype.card {i // i ∉ M}

def selectedIndex {n : Nat} (M : Finset (Fin n)) :
    Fin (selectedCount M) ≃ {i // i ∈ M} := (Fintype.equivFin _).symm

def remainderIndex {n : Nat} (M : Finset (Fin n)) :
    Fin (remainderCount M) ≃ {i // i ∉ M} := (Fintype.equivFin _).symm

def split {n : Nat} (M : Finset (Fin n)) (x : (qubits n).Basis) :
    (qubits (selectedCount M)).Basis × (qubits (remainderCount M)).Basis :=
  (writeBits _ (fun i => readBits x (selectedIndex M i).val),
    writeBits _ (fun i => readBits x (remainderIndex M i).val))

def join {n : Nat} (M : Finset (Fin n))
    (p : (qubits (selectedCount M)).Basis × (qubits (remainderCount M)).Basis) : (qubits n).Basis :=
  writeBits n (fun i => if h : i ∈ M then readBits p.1 ((selectedIndex M).symm ⟨i,h⟩)
    else readBits p.2 ((remainderIndex M).symm ⟨i,h⟩))

theorem join_split {n : Nat} (M : Finset (Fin n)) (x : (qubits n).Basis) :
    join M (split M x) = x := by
  apply (bitStringEquiv n).injective
  change readBits (join M (split M x)) = readBits x
  funext i
  simp only [join, read_write]
  by_cases h : i ∈ M
  · simp [h, split, read_write]
  · simp [h, split, read_write]

theorem split_join {n : Nat} (M : Finset (Fin n))
    (p : (qubits (selectedCount M)).Basis × (qubits (remainderCount M)).Basis) :
    split M (join M p) = p := by
  apply Prod.ext
  · apply (bitStringEquiv (selectedCount M)).injective
    change readBits (split M (join M p)).1 = readBits p.1
    funext i
    simp [split, join, read_write]
  · apply (bitStringEquiv (remainderCount M)).injective
    change readBits (split M (join M p)).2 = readBits p.2
    funext i
    simp [split, join, read_write, (remainderIndex M i).property]

def splitEquiv {n : Nat} (M : Finset (Fin n)) : (qubits n).Basis ≃
    (Space.tensor (qubits (selectedCount M)) (qubits (remainderCount M))).Basis where
  toFun := split M
  invFun := join M
  left_inv := join_split M
  right_inv := split_join M

abbrev signalSpace (n : Nat) := Space.tensor (qubits n) (qubits n)
abbrev auxiliary {n : Nat} (M : Finset (Fin n)) (e : Space) :=
  Space.tensor (signalSpace (remainderCount M)) e

/-- Separate matched Bob/Alice signals while keeping both unmatched signals
and Eve. This channel is a permutation, not a measurement or cloning map. -/
def jointEquiv {n : Nat} (M : Finset (Fin n)) (e : Space) :
    (Space.tensor (signalSpace n) e).Basis ≃
      (Space.tensor (signalSpace (selectedCount M)) (auxiliary M e)).Basis where
  toFun p := (((splitEquiv M p.1.1).1,(splitEquiv M p.1.2).1),
    (((splitEquiv M p.1.1).2,(splitEquiv M p.1.2).2),p.2))
  invFun p := (((splitEquiv M).symm (p.1.1,p.2.1.1),
    (splitEquiv M).symm (p.1.2,p.2.1.2)),p.2.2)
  left_inv p := by
    rcases p with ⟨⟨b,a⟩,u⟩
    simp only [Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv p := by
    rcases p with ⟨⟨b,a⟩,⟨⟨r,s⟩,u⟩⟩
    simp only [Equiv.apply_symm_apply]

def input {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n)) :
    Density (.tensor (signalSpace (selectedCount M)) (auxiliary M e)) :=
  (BasisChannel.channel (jointEquiv M e)).run (BB84PreparedInput.input A)

theorem input_entry {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (p q : (Space.tensor (signalSpace (selectedCount M)) (auxiliary M e)).Basis) :
    (input A M).matrix p q =
      (BB84PreparedInput.input A).matrix ((jointEquiv M e).symm p) ((jointEquiv M e).symm q) := by
  change (BasisChannel.channel (jointEquiv M e)).toKraus.apply _ p q = _
  rw [BasisChannel.apply]
  rfl

def bases {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis) :
    Fin (selectedCount M) → BB84Basis := fun i => θ (selectedIndex M i).val

theorem common_bases {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis) :
    bases M (BB84SiftingRandomness.bobBases θ M) = bases M θ := by
  funext i
  simp [bases, BB84SiftingRandomness.bobBases, (selectedIndex M i).property]

/-- Interpret the already sound finite error-first derivation on the actual
selected source, with all unmatched signals retained in the auxiliary space. -/
theorem interpreted {n : Nat} {e : Space} (A : BlockAttack n e) (M : Finset (Fin n))
    (θ : Fin n → BB84Basis) (T : Finset (Fin (selectedCount M))) (minKey tolerance : Nat) :
    (BB84CNOTLogic.model (input A M)
      (fun _ => Channel.identity (BB84CNOTLogic.recordSpace (selectedCount M) (auxiliary M e)))).Carrier
      (.decidedRaw (bases M θ) T minKey tolerance) :=
  BB84CNOTLogic.sound _ _ (BB84CNOTLogic.decidedRawProof (bases M θ) T minKey tolerance)
    (fun i => Fin.elim0 i)

end
end Foundation.Quantum.QKD.BB84SiftedInput
