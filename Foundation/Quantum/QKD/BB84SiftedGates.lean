import Foundation.Quantum.QKD.BB84SiftedInput

/-! Local basis gates respect the physical selection of matched positions.
The discarded positions are still quantum auxiliaries, with their own basis
operations; no product-state assumption occurs in these identities. -/
namespace Foundation.Quantum.QKD.BB84SiftedInput
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem gate_entry (n : Nat) (θ : Fin n → BB84Basis) (x y : (qubits n).Basis) :
    blockGate n θ x y = ∏ i, bitGate (θ i) (readBits x i) (readBits y i) := by
  induction n with
  | zero => cases x; cases y; simp [blockGate]
  | succ n ih =>
    rcases x with ⟨b,x⟩
    rcases y with ⟨a,y⟩
    change bitGate (θ 0) b a * blockGate n (fun i => θ i.succ) x y = _
    rw [Fin.prod_univ_succ, ih]
    rfl

theorem product_split {n : Nat} (M : Finset (Fin n)) (f : Fin n → ℂ) :
    (∏ i, f i) = (∏ i, f (selectedIndex M i).val) *
      (∏ i, f (remainderIndex M i).val) := by
  rw [Equiv.prod_comp (selectedIndex M) (fun i => f i.val),
    Equiv.prod_comp (remainderIndex M) (fun i => f i.val)]
  convert (Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ M) f).symm using 1
  apply congrArg₂ (fun x y : ℂ => x*y)
  · apply Finset.prod_congr
    · ext i; simp
    · intro i _; rfl
  · rfl

def remainderBases {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis) :
    Fin (remainderCount M) → BB84Basis := fun i => θ (remainderIndex M i).val

theorem split_gate_entry {n : Nat} (M : Finset (Fin n)) (θ : Fin n → BB84Basis)
    (x y : (qubits n).Basis) :
    blockGate n θ x y =
      blockGate (selectedCount M) (bases M θ) (split M x).1 (split M y).1 *
        blockGate (remainderCount M) (remainderBases M θ) (split M x).2 (split M y).2 := by
  simp only [gate_entry, bases, remainderBases, split, read_write]
  exact product_split M _

def fullGate {n : Nat} (bob alice : Fin n → BB84Basis) (e : Space) :
    Operator (.tensor (signalSpace n) e) :=
  Op.tensor (Op.tensor (blockGate n bob) (blockGate n alice)) (Op.ident e)

def selectedGate {n : Nat} (M : Finset (Fin n)) (bob alice : Fin n → BB84Basis) (e : Space) :
    Operator (.tensor (signalSpace (selectedCount M)) (auxiliary M e)) :=
  Op.tensor
    (Op.tensor (blockGate (selectedCount M) (bases M bob)) (blockGate (selectedCount M) (bases M alice)))
    (Op.tensor
      (Op.tensor (blockGate (remainderCount M) (remainderBases M bob))
        (blockGate (remainderCount M) (remainderBases M alice))) (Op.ident e))

theorem gate_operation {n : Nat} (M : Finset (Fin n)) (bob alice : Fin n → BB84Basis) (e : Space) :
    selectedGate M bob alice e * Op.basisMap (jointEquiv M e) =
      Op.basisMap (jointEquiv M e) * fullGate bob alice e := by
  change Op.seq (Op.basisMap (jointEquiv M e)) (selectedGate M bob alice e) =
    Op.seq (fullGate bob alice e) (Op.basisMap (jointEquiv M e))
  rw [Op.basisMap_seq, Op.seq_basisEquiv]
  apply Matrix.ext
  intro i j
  obtain ⟨i,rfl⟩ := (jointEquiv M e).surjective i
  rcases i with ⟨⟨b,a⟩,u⟩
  rcases j with ⟨⟨c,d⟩,v⟩
  simp only [Equiv.symm_apply_apply]
  change
    (blockGate _ (bases M bob) (split M b).1 (split M c).1 *
      blockGate _ (bases M alice) (split M a).1 (split M d).1) *
      ((blockGate _ (remainderBases M bob) (split M b).2 (split M c).2 *
        blockGate _ (remainderBases M alice) (split M a).2 (split M d).2) * (Op.ident e) u v) =
    (blockGate n bob b c * blockGate n alice a d) * (Op.ident e) u v
  rw [split_gate_entry M bob, split_gate_entry M alice]
  ring

theorem fullGate_isometry {n : Nat} (bob alice : Fin n → BB84Basis) (e : Space) :
    (fullGate bob alice e).conjTranspose * fullGate bob alice e = 1 :=
  tensor_isometry _ _ (tensor_isometry _ _ (blockGate_isometry _ _) (blockGate_isometry _ _))
    (by simp [Op.ident])

theorem selectedGate_isometry {n : Nat} (M : Finset (Fin n))
    (bob alice : Fin n → BB84Basis) (e : Space) :
    (selectedGate M bob alice e).conjTranspose * selectedGate M bob alice e = 1 :=
  tensor_isometry _ _ (tensor_isometry _ _ (blockGate_isometry _ _) (blockGate_isometry _ _))
    (tensor_isometry _ _ (tensor_isometry _ _ (blockGate_isometry _ _) (blockGate_isometry _ _))
      (by simp [Op.ident]))

def fullChannel {n : Nat} (bob alice : Fin n → BB84Basis) (e : Space) :=
  Channel.ofIsometry (fullGate bob alice e) (fullGate_isometry bob alice e)

def selectedChannel {n : Nat} (M : Finset (Fin n)) (bob alice : Fin n → BB84Basis) (e : Space) :=
  Channel.ofIsometry (selectedGate M bob alice e) (selectedGate_isometry M bob alice e)

/-- The full physical basis operation can be performed after the signal
selection, including the still quantum unmatched subsystem. -/
theorem gate_apply {n : Nat} (M : Finset (Fin n)) (bob alice : Fin n → BB84Basis) (e : Space)
    (ρ : Operator (.tensor (signalSpace n) e)) :
    (BasisChannel.channel (jointEquiv M e)).toKraus.apply
      ((fullChannel bob alice e).toKraus.apply ρ) =
    (selectedChannel M bob alice e).toKraus.apply
      ((BasisChannel.channel (jointEquiv M e)).toKraus.apply ρ) := by
  simp only [fullChannel, selectedChannel, BasisChannel.channel, Channel.ofIsometry, Kraus.single_apply]
  calc
    _ = (Op.basisMap (jointEquiv M e) * fullGate bob alice e) * ρ *
        (Op.basisMap (jointEquiv M e) * fullGate bob alice e).conjTranspose := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (selectedGate M bob alice e * Op.basisMap (jointEquiv M e)) * ρ *
        (selectedGate M bob alice e * Op.basisMap (jointEquiv M e)).conjTranspose := by
      rw [← gate_operation]
    _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end
end Foundation.Quantum.QKD.BB84SiftedInput
