import Foundation.Quantum.QKD.PairwiseRandomizedLogic
import Foundation.Quantum.QKD.BB84PhaseSupport

/-! Reversible error/key coordinates for the fixed-reference pair experiment.
The physical key-side gate becomes identity on error coordinates and a full
Hadamard on complementary key coordinates, for every mixed basis string. -/
namespace Foundation.Quantum.QKD.PairwisePhaseCoordinates
noncomputable section
open BB84ErrorTransform BB84PairwiseReference
set_option backward.isDefEq.respectTransparency false

abbrev signal (n : Nat) := Space.tensor (qubits n) (qubits n)

def split : (n : Nat) → (Fin n → BB84Basis) → (signal n).Basis → (signal n).Basis
  | 0, _, p => p
  | n+1, θ, ((b,v),(a,w)) =>
    let q := split n (fun i => θ i.succ) (v,w)
    match θ 0 with
    | .Z => ((b,q.1),(a,q.2))
    | .X => ((a,q.1),(b,q.2))

theorem split_involution (n : Nat) (θ : Fin n → BB84Basis) (p : (signal n).Basis) :
    split n θ (split n θ p) = p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨⟨b,v⟩,⟨a,w⟩⟩
    have h := ih (fun i => θ i.succ) (v,w)
    cases hθ : θ 0 <;> simp only [split, hθ]
    · exact congrArg (fun q => ((b,q.1),(a,q.2))) h
    · exact congrArg (fun q => ((b,q.1),(a,q.2))) h

def equivalence (n : Nat) (θ : Fin n → BB84Basis) : (signal n).Basis ≃ (signal n).Basis where
  toFun := split n θ
  invFun := split n θ
  left_inv := split_involution n θ
  right_inv := split_involution n θ

theorem bits (n : Nat) (θ : Fin n → BB84Basis) (p : (signal n).Basis) :
    readBits (split n θ p).1 = errorBits θ p ∧ readBits (split n θ p).2 = keyBits θ p := by
  induction n with
  | zero => constructor <;> funext i <;> exact Fin.elim0 i
  | succ n ih =>
    rcases p with ⟨⟨b,v⟩,⟨a,w⟩⟩
    have h := ih (fun i => θ i.succ) (v,w)
    constructor
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · cases hθ : θ 0 <;> simp [split, hθ, errorBits, readBits]
      · cases hθ : θ 0 <;> simpa only [split, hθ, readBits, Fin.cases_succ, errorBits] using congrFun h.1 j
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · cases hθ : θ 0 <;> simp [split, hθ, keyBits, readBits]
      · cases hθ : θ 0 <;> simpa only [split, hθ, readBits, Fin.cases_succ, keyBits] using congrFun h.2 j

/-- The exact coefficient identity for the actual mixed-basis key operation. -/
theorem key_coefficient (n : Nat) (θ : Fin n → BB84Basis) (p q : (signal n).Basis) :
    keyGate θ p q =
      (if (split n θ p).1 = (split n θ q).1 then 1 else 0) *
        PhaseSupport.gate n (split n θ p).2 (split n θ q).2 := by
  induction n with
  | zero => rcases p with ⟨⟨⟩,⟨⟩⟩; rcases q with ⟨⟨⟩,⟨⟩⟩; norm_num [keyGate, split, PhaseSupport.gate, blockGate, Op.tensor, Matrix.one_apply]
  | succ n ih =>
    rcases p with ⟨⟨b,v⟩,⟨a,w⟩⟩
    rcases q with ⟨⟨i,l⟩,⟨j,m⟩⟩
    have h := ih (fun z => θ z.succ) (v,w) (l,m)
    have he : keyGate θ ((b,v),(a,w)) ((i,l),(j,m)) =
        (bitGate (θ 0) b i * bitGate (BB84SiftingRandomness.opposite (θ 0)) a j) *
          keyGate (fun z => θ z.succ) (v,w) (l,m) := by
      change (bitGate (θ 0) b i * blockGate n (fun z => θ z.succ) v l) *
        (bitGate (BB84SiftingRandomness.opposite (θ 0)) a j *
          blockGate n (fun z => BB84SiftingRandomness.opposite (θ z.succ)) w m) = _
      change _ = (bitGate (θ 0) b i * bitGate (BB84SiftingRandomness.opposite (θ 0)) a j) *
        (blockGate n (fun z => θ z.succ) v l *
          blockGate n (fun z => BB84SiftingRandomness.opposite (θ z.succ)) w m)
      ring
    have hp (b i : Fin 2) (x y : (qubits n).Basis) :
        (((b,x) : (qubits (n+1)).Basis) = (i,y)) ↔ b = i ∧ x = y := by
      change (b,x) = (i,y) ↔ _
      simp only [Prod.mk.injEq]
    rw [he, h]
    cases hθ : θ 0 <;>
      simp only [split, hθ, BB84SiftingRandomness.opposite, bitGate, Matrix.one_apply,
        PhaseSupport.gate, blockGate, Op.tensor, Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply,
        hp]
    all_goals split_ifs <;> simp_all

end
end Foundation.Quantum.QKD.PairwisePhaseCoordinates
