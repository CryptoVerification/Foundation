import Foundation.Quantum.QKD.BB84SourceReplacement

/-! The controlled-NOT change of experiment in Bouman--Fehr, §6, equations
(2)--(3), for arbitrary block length and mixed common BB84 bases. Here the
first factor is Bob and the second Alice. Arbitrary quantum auxiliaries can
be retained by amplification. -/
namespace Foundation.Quantum.QKD.BB84ErrorTransform
noncomputable section
set_option backward.isDefEq.respectTransparency false

def bitXor (a b : Fin 2) : Fin 2 := if a = b then 0 else 1

theorem bitXor_cancel (a b : Fin 2) : bitXor (bitXor a b) b = a := by
  fin_cases a <;> fin_cases b <;> decide

theorem bitXor_comm (a b : Fin 2) : bitXor a b = bitXor b a := by
  fin_cases a <;> fin_cases b <;> decide

def xor : (n : Nat) → (qubits n).Basis → (qubits n).Basis → (qubits n).Basis
  | 0, _, _ => ()
  | n+1, (b,v), (a,w) => (bitXor b a, xor n v w)

theorem xor_cancel (n : Nat) (b a : (qubits n).Basis) : xor n (xor n b a) a = b := by
  induction n with
  | zero => cases b; rfl
  | succ n ih =>
    rcases b with ⟨b,v⟩
    rcases a with ⟨a,w⟩
    simp only [xor, bitXor_cancel, ih]

def relabel : (n : Nat) → (Fin n → BB84Basis) →
    (qubits n).Basis × (qubits n).Basis → (qubits n).Basis × (qubits n).Basis
  | 0, _, p => p
  | n+1, θ, ((b,v),(a,w)) =>
    let q := relabel n (fun i => θ i.succ) (v,w)
    match θ 0 with
    | .Z => ((bitXor b a,q.1),(a,q.2))
    | .X => ((b,q.1),(bitXor a b,q.2))

theorem relabel_involution (n : Nat) (θ : Fin n → BB84Basis)
    (p : (qubits n).Basis × (qubits n).Basis) : relabel n θ (relabel n θ p) = p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨⟨b,v⟩,⟨a,w⟩⟩
    have h := ih (fun i => θ i.succ) (v,w)
    cases hθ : θ 0 <;> simp only [relabel, hθ, bitXor_cancel]
    · exact congrArg (fun q => ((b,q.1),(a,q.2))) h
    · exact congrArg (fun q => ((b,q.1),(a,q.2))) h

def cnotEquiv (n : Nat) : (Space.tensor (qubits n) (qubits n)).Basis ≃
    (Space.tensor (qubits n) (qubits n)).Basis where
  toFun p := (xor n p.1 p.2,p.2)
  invFun p := (xor n p.1 p.2,p.2)
  left_inv p := by simp only [xor_cancel]
  right_inv p := by simp only [xor_cancel]

def relabelEquiv (n : Nat) (θ : Fin n → BB84Basis) :
    (Space.tensor (qubits n) (qubits n)).Basis ≃ (Space.tensor (qubits n) (qubits n)).Basis where
  toFun := relabel n θ
  invFun := relabel n θ
  left_inv := relabel_involution n θ
  right_inv := relabel_involution n θ

theorem read_relabel (n : Nat) (θ : Fin n → BB84Basis) (b a : (qubits n).Basis) (i : Fin n) :
    readBits (relabel n θ (b,a)).1 i =
        (if θ i = .Z then bitXor (readBits b i) (readBits a i) else readBits b i) ∧
      readBits (relabel n θ (b,a)).2 i =
        (if θ i = .X then bitXor (readBits a i) (readBits b i) else readBits a i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rcases b with ⟨b,v⟩
    rcases a with ⟨a,w⟩
    refine Fin.cases ?_ (fun k => ?_) i
    · cases hθ : θ 0 <;> simp [relabel, readBits, hθ]
    · have h := ih (fun k => θ k.succ) v w k
      cases hθ : θ 0 <;> simpa only [relabel, hθ, readBits, Fin.cases_succ] using h

def errorBits {n : Nat} (θ : Fin n → BB84Basis) (p : (qubits n).Basis × (qubits n).Basis) : Fin n → Fin 2 :=
  fun i => if θ i = .Z then readBits p.1 i else readBits p.2 i

def keyBits {n : Nat} (θ : Fin n → BB84Basis) (p : (qubits n).Basis × (qubits n).Basis) : Fin n → Fin 2 :=
  fun i => if θ i = .Z then readBits p.2 i else readBits p.1 i

theorem errorBits_relabel (n : Nat) (θ : Fin n → BB84Basis) (b a : (qubits n).Basis) :
    errorBits θ (relabel n θ (b,a)) = fun i => bitXor (readBits b i) (readBits a i) := by
  funext i
  simp only [errorBits]
  have h := read_relabel n θ b a i
  cases hθ : θ i <;> simp only [hθ, reduceCtorEq, ite_true, ite_false] at h ⊢
  · exact h.1
  · exact h.2.trans (bitXor_comm _ _)

theorem keyBits_relabel (n : Nat) (θ : Fin n → BB84Basis) (b a : (qubits n).Basis) :
    keyBits θ (relabel n θ (b,a)) = fun i => if θ i = .Z then readBits a i else readBits b i := by
  funext i
  simp only [keyBits]
  have h := read_relabel n θ b a i
  cases hθ : θ i <;> simp only [hθ, reduceCtorEq, ite_true, ite_false] at h ⊢
  · exact h.2
  · exact h.1

theorem bit_coefficient (θ : BB84Basis) (b a i j : Fin 2) :
    bitGate θ b (bitXor i j) * bitGate θ a j =
      bitGate θ (if θ = .Z then bitXor b a else b) i *
        bitGate θ (if θ = .X then bitXor a b else a) j := by
  cases θ <;> simp only [reduceCtorEq, ite_true, ite_false] <;> fin_cases b <;> fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [bitGate, bitXor, hadamard, Matrix.one_apply]

theorem block_coefficient (n : Nat) (θ : Fin n → BB84Basis)
    (b a i j : (qubits n).Basis) :
    blockGate n θ b (xor n i j) * blockGate n θ a j =
      blockGate n θ (relabel n θ (b,a)).1 i * blockGate n θ (relabel n θ (b,a)).2 j := by
  induction n with
  | zero => cases b; cases a; cases i; cases j; rfl
  | succ n ih =>
    rcases b with ⟨b,v⟩
    rcases a with ⟨a,w⟩
    rcases i with ⟨i,s⟩
    rcases j with ⟨j,t⟩
    have hb := bit_coefficient (θ 0) b a i j
    have hh := ih (fun k => θ k.succ) v w s t
    cases hθ : θ 0 <;>
      simp only [hθ, reduceCtorEq, ite_true, ite_false] at hb
    · simp only [blockGate, xor, relabel, hθ, Op.tensor, Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply]
      calc
        _ = (bitGate .Z b (bitXor i j) * bitGate .Z a j) *
            (blockGate n (fun k => θ k.succ) v (xor n s t) * blockGate n (fun k => θ k.succ) w t) := by ring
        _ = _ := by rw [hb, hh]; ring
    · simp only [blockGate, xor, relabel, hθ, Op.tensor, Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply]
      calc
        _ = (bitGate .X b (bitXor i j) * bitGate .X a j) *
            (blockGate n (fun k => θ k.succ) v (xor n s t) * blockGate n (fun k => θ k.succ) w t) := by ring
        _ = _ := by rw [hb, hh]; ring

def basisGate (n : Nat) (θ : Fin n → BB84Basis) : Operator (.tensor (qubits n) (qubits n)) :=
  Op.tensor (blockGate n θ) (blockGate n θ)

/-- Exact operation equality before any quantum state or attacker is fixed. -/
theorem operation (n : Nat) (θ : Fin n → BB84Basis) :
    basisGate n θ * Op.basisMap (cnotEquiv n) =
      Op.basisMap (relabelEquiv n θ) * basisGate n θ := by
  change Op.seq (Op.basisMap (cnotEquiv n)) (basisGate n θ) =
    Op.seq (basisGate n θ) (Op.basisMap (relabelEquiv n θ))
  rw [Op.basisMap_seq, Op.seq_basisEquiv]
  ext ⟨b,a⟩ ⟨i,j⟩
  exact block_coefficient n θ b a i j

end
end Foundation.Quantum.QKD.BB84ErrorTransform
