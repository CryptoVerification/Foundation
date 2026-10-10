import Foundation.Quantum.QKD.BB84RawProtocol

/-! A genuinely joint two-signal attack, not a tensor product of single-signal
operators. Classical CNOT extends linearly to quantum inputs and is not an
unknown-state cloning operation. -/
namespace Foundation.Quantum.QKD.BlockExamples
noncomputable section
set_option backward.isDefEq.respectTransparency false

def controlledNot (b : (qubits 2).Basis) : (qubits 2).Basis :=
  (b.1, (if b.1 = 0 then b.2.1 else 1 - b.2.1, b.2.2))

theorem controlledNot_involutive : Function.Involutive controlledNot := by
  rintro ⟨c,t,u⟩
  cases u
  fin_cases c <;> fin_cases t <;> rfl

def controlledNotEquiv : (qubits 2).Basis ≃ (qubits 2).Basis :=
  ⟨controlledNot, controlledNot, controlledNot_involutive, controlledNot_involutive⟩

theorem basisEquiv_isometry {a : Space} (f : a.Basis ≃ a.Basis) :
    (Op.basisMap f).conjTranspose * Op.basisMap f = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [Op.basisMap, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite]
  · have hf : f i ≠ f j := fun hh => h (f.injective hh)
    simp [Op.basisMap, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite,
      h, hf, eq_comm]

def cnot : Operator (qubits 2) := Op.basisMap controlledNotEquiv

theorem cnot_isometry : cnot.conjTranspose * cnot = 1 := basisEquiv_isometry controlledNotEquiv

/-- The second signal really depends on the first; independent operations cannot realize this attack. -/
theorem cnot_not_product (M : Operator .bit) (N : Operator (qubits 1)) : cnot ≠ Op.tensor M N := by
  intro h
  have h00 := congrFun (congrFun h (0,(0,()))) (0,(0,()))
  have h01 := congrFun (congrFun h (0,(1,()))) (0,(0,()))
  have h11 := congrFun (congrFun h (1,(1,()))) (1,(0,()))
  change (1 : ℂ) = M 0 0 * N (0,()) (0,()) at h00
  change (0 : ℂ) = M 0 0 * N (1,()) (0,()) at h01
  change (1 : ℂ) = M 1 1 * N (1,()) (0,()) at h11
  rcases mul_eq_zero.mp h01.symm with hm | hn
  · simp [hm] at h00
  · simp [hn] at h11

def appendUnit (a : Space) : Op a (.tensor a .unit) :=
  fun i j => if i.1 = j then 1 else 0

theorem appendUnit_isometry (a : Space) : (appendUnit a).conjTranspose * appendUnit a = 1 := by
  ext i j
  simp [appendUnit, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite, eq_comm]

/-- A valid block attack with a retained environment interface. -/
def cnotAttack : BlockAttack 2 .unit := Channel.ofIsometry (appendUnit (qubits 2) * cnot)
  (isometry_lift_seq cnot (appendUnit (qubits 2)) cnot_isometry (appendUnit_isometry _))

/-- Sifting omits every tested position, even in the accepted no-error case. -/
example : (RawProtocol.output (n := 2) (fun _ => .Z) (fun _ => .Z)
    (fun _ => 0) (fun _ => 0) {0} 1 0).aliceKey 0 = none := by
  exact (RawProtocol.tested_not_key _ _ _ _ _ _ _ _ (by simp)).1

/-- A malformed test mask cannot yield private keys. -/
example : (RawProtocol.output (n := 1) (fun _ => .Z) (fun _ => .X)
    (fun _ => 0) (fun _ => 0) {0} 0 0).aliceKey = (fun _ => none) := by
  apply (RawProtocol.abort_keys _ _ _ _ _ _ _ _).1
  decide

end
end Foundation.Quantum.QKD.BlockExamples
