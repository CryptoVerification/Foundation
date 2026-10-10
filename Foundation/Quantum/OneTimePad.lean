import Foundation.Quantum.Channels

/-! A concrete perfect-private quantum channel: averaging the four Pauli
keys. The two key bits are uniform, secret, and independent of the input and
auxiliary system. This is a one-use encryption example, not a QKD security proof. -/
namespace Foundation.Quantum.OneTimePad
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

/-- A phase followed by a bit flip. -/
def pauli (u v : Fin 2) : Op .bit .bit :=
  fun i j => if i = j + u then (if v = 1 ∧ j = 1 then -1 else 1) else 0

theorem pauli_isometry (u v : Fin 2) : (pauli u v).conjTranspose * pauli u v = 1 := by
  ext i j
  change (∑ k : Fin 2, star (pauli u v k i) * pauli u v k j) = if i = j then 1 else 0
  fin_cases u <;> fin_cases v <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauli, Fin.sum_univ_two]

def encrypt (u v : Fin 2) : Channel .bit .bit := Channel.ofIsometry (pauli u v) (pauli_isometry u v)

/-- Reversing the coherent operation decrypts every density operator. -/
theorem decrypt_encrypt (u v : Fin 2) (ρ : Operator .bit) :
    (pauli u v).conjTranspose * ((pauli u v) * ρ * (pauli u v).conjTranspose) * pauli u v = ρ := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, pauli_isometry, Matrix.one_mul,
    Matrix.mul_assoc, pauli_isometry, Matrix.mul_one]

/-- Each amplitude is one half, so each hidden key has probability one quarter. -/
def average : Channel .bit .bit where
  index := Fin 2 × Fin 2
  finite := inferInstance
  operator p := (1 / 2 : ℂ) • pauli p.1 p.2
  complete := by
    ext i j
    change (∑ p : Fin 2 × Fin 2,
      (((1 / 2 : ℂ) • pauli p.1 p.2).conjTranspose *
        ((1 / 2 : ℂ) • pauli p.1 p.2)) i j) = if i = j then 1 else 0
    fin_cases i <;> fin_cases j <;>
      norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.mul_apply,
        Matrix.conjTranspose_apply, pauli, Matrix.smul_apply, map_ofNat]

/-- The ideal channel discards the input and prepares a uniform classical bit.
Duplicate Kraus indices avoid choosing square roots in this concrete representation. -/
def ideal : Channel .bit .bit where
  index := Fin 2 × Fin 2 × Fin 2
  finite := inferInstance
  operator p := fun i j => if i = p.1 ∧ j = p.2.1 then (1 / 2 : ℂ) else 0
  complete := by
    ext i j
    change (∑ p : Fin 2 × Fin 2 × Fin 2, ∑ k : Fin 2,
      star (if k = p.1 ∧ i = p.2.1 then (1 / 2 : ℂ) else 0) *
        (if k = p.1 ∧ j = p.2.1 then (1 / 2 : ℂ) else 0)) = if i = j then 1 else 0
    fin_cases i <;> fin_cases j <;>
      norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, map_ofNat]

/-- Exact twirling identity, retaining every matrix element of the auxiliary system. -/
theorem average_auxiliary (e : Space) (ρ : Operator (.tensor .bit e))
    (i j : Fin 2) (u v : e.Basis) :
    (average.amplify e).toKraus.apply ρ (i, u) (j, v) =
      if i = j then (ρ (0, u) (0, v) + ρ (1, u) (1, v)) / 2 else 0 := by
  change (average.toKraus.amplify e).apply ρ (i, u) (j, v) = _
  rw [Kraus.amplify_apply_entry]
  dsimp [average]
  fin_cases i <;> fin_cases j <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, pauli, map_ofNat] <;> ring

theorem ideal_auxiliary (e : Space) (ρ : Operator (.tensor .bit e))
    (i j : Fin 2) (u v : e.Basis) :
    (ideal.amplify e).toKraus.apply ρ (i, u) (j, v) =
      if i = j then (ρ (0, u) (0, v) + ρ (1, u) (1, v)) / 2 else 0 := by
  change (ideal.toKraus.amplify e).apply ρ (i, u) (j, v) = _
  rw [Kraus.amplify_apply_entry]
  dsimp [ideal]
  fin_cases i <;> fin_cases j <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, map_ofNat] <;> ring

/-- Perfect one-use privacy, quantified over all finite entangled inputs and binary tests. -/
theorem perfect_privacy : Approx average ideal 0 := by
  intro e ρ E
  have h : ((average.amplify e).run ρ).matrix = ((ideal.amplify e).run ρ).matrix := by
    ext ⟨i, u⟩ ⟨j, v⟩
    exact (average_auxiliary e ρ.matrix i j u v).trans (ideal_auxiliary e ρ.matrix i j u v).symm
  unfold Effect.probability
  rw [h]
  simp

end
end Foundation.Quantum.OneTimePad
