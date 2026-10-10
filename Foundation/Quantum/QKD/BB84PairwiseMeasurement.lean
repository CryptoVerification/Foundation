import Foundation.Quantum.QKD.BB84PairwiseReference

/-! Error-side measurement in the fixed Bob-Z/Alice-X reference basis.
The physical key-side rotation commutes with every error branch; it can be
performed after that measurement while retaining the whole quantum state. -/
namespace Foundation.Quantum.QKD.BB84PairwiseReference
noncomputable section
open BB84ErrorTransform BB84DelayedMeasurements PartitionMeasurement QuantumErrorTest
set_option backward.isDefEq.respectTransparency false

theorem mask_commutes {n : Nat} (θ : Fin n → BB84Basis) (e : Space) (r : Fin (count n)) :
    Op.tensor (keyGate θ) (Op.ident e) * mask (fun i => errorLabel θ (e := e) i = r) =
      mask (fun i => errorLabel θ (e := e) i = r) * Op.tensor (keyGate θ) (Op.ident e) := by
  ext i j
  simp only [mask, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hg : Op.tensor (keyGate θ) (Op.ident e) i j = 0
  · simp only [hg, zero_mul, mul_zero]
  · have hkey : keyGate θ i.1 j.1 ≠ 0 := (mul_ne_zero_iff.mp hg).1
    have he : errorLabel θ (e := e) i = errorLabel θ (e := e) j :=
      congrArg (Fintype.equivFin (Fin n → Fin 2)) (key_support θ i.1 j.1 hkey)
    simp only [he, mul_comm]

/-- Every subnormalized outcome branch, without division by its probability. -/
theorem branch_key {n : Nat} (θ : Fin n → BB84Basis) (e : Space)
    (ρ : Operator (jointSpace n e)) (r : Fin (count n)) :
    ((instrument (errorLabel θ (e := e))).branch r).apply
      (((keyChannel θ).amplify e).toKraus.apply ρ) =
      ((keyChannel θ).amplify e).toKraus.apply
        (((instrument (errorLabel θ (e := e))).branch r).apply ρ) := by
  change (Kraus.single (mask (fun i => errorLabel θ (e := e) i = r))).apply
    ((Kraus.single (Op.tensor (keyGate θ) (Op.ident e))).apply ρ) =
    (Kraus.single (Op.tensor (keyGate θ) (Op.ident e))).apply
      ((Kraus.single (mask (fun i => errorLabel θ (e := e) i = r))).apply ρ)
  simp only [Kraus.single_apply]
  calc
    _ = (mask (fun i => errorLabel θ (e := e) i = r) * Op.tensor (keyGate θ) (Op.ident e)) * ρ *
        (mask (fun i => errorLabel θ (e := e) i = r) * Op.tensor (keyGate θ) (Op.ident e)).conjTranspose := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (Op.tensor (keyGate θ) (Op.ident e) * mask (fun i => errorLabel θ (e := e) i = r)) * ρ *
        (Op.tensor (keyGate θ) (Op.ident e) * mask (fun i => errorLabel θ (e := e) i = r)).conjTranspose := by
      rw [← mask_commutes]
    _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Recording the actual common-basis error measurement equals measuring in
the fixed reference coordinates and then rotating only the unmeasured keys. -/
theorem first_reference {n : Nat} (θ : Fin n → BB84Basis) (e : Space)
    (ρ : Operator (jointSpace n e)) :
    ((instrument (errorLabel θ (e := e))).pre ((BB84ErrorTransform.basisChannel n θ).amplify e)).record.toKraus.apply ρ =
      (((instrument (errorLabel θ (e := e))).post ((keyChannel θ).amplify e)).pre
        ((referenceChannel n).amplify e)).record.toKraus.apply ρ := by
  apply Instrument.record_congr
  intro r
  rw [Instrument.pre_apply, Instrument.pre_apply, Instrument.post_apply, basis_factor, branch_key]

/-- The input to the fixed-reference measurement is chosen before the random
basis selector. Its CNOT and reference-basis operations do not depend on θ. -/
def referenceInput {n : Nat} {e : Space} (ρ : Density (jointSpace n e)) :=
  ((referenceChannel n).amplify e).run (((cnotChannel n).amplify e).run ρ)

def actualFirst {n : Nat} (θ : Fin n → BB84Basis) (e : Space) :=
  (instrument (errorLabel θ (e := e))).pre ((original n θ).amplify e)

def referenceFirst {n : Nat} (θ : Fin n → BB84Basis) (e : Space) :=
  ((instrument (errorLabel θ (e := e))).post ((keyChannel θ).amplify e)).pre
    (((cnotChannel n).amplify e).seq ((referenceChannel n).amplify e))

/-- The full classical error record and every remaining quantum coordinate
agree with the actual CNOT experiment used in the existing closed derivation. -/
theorem actual_reference {n : Nat} (θ : Fin n → BB84Basis) (e : Space)
    (ρ : Operator (jointSpace n e)) :
    (actualFirst θ e).record.toKraus.apply ρ = (referenceFirst θ e).record.toKraus.apply ρ := by
  apply Instrument.record_congr
  intro r
  simp only [actualFirst, referenceFirst, Instrument.pre_apply, Instrument.post_apply,
    Channel.seq, Kraus.seq_apply, original, Channel.amplify, Kraus.amplify_seq]
  have h := basis_factor θ e (((cnotChannel n).amplify e).toKraus.apply ρ)
  exact (congrArg ((instrument (errorLabel θ (e := e))).branch r).apply h).trans
    (branch_key θ e (((referenceChannel n).amplify e).toKraus.apply
      (((cnotChannel n).amplify e).toKraus.apply ρ)) r)

/-- Identify the instrument formulation with the actual first-measurement
channel already used in the verified delayed BB84 experiment. -/
theorem actual_delayed_first {n : Nat} (θ : Fin n → BB84Basis) (e : Space)
    (ρ : Operator (jointSpace n e)) :
    (actualFirst θ e).record.toKraus.apply ρ =
      (BB84DelayedMeasurements.first θ e).toKraus.apply
        (((original n θ).amplify e).toKraus.apply ρ) := by
  ext ⟨r,i⟩ ⟨s,j⟩
  by_cases h : r = s
  · subst s
    rw [Instrument.record_diagonal]
    change ((actualFirst θ e).branch r).apply ρ i j =
      (instrument (errorLabel θ (e := e))).record.toKraus.apply
        (((original n θ).amplify e).toKraus.apply ρ) (r,i) (r,j)
    rw [Instrument.record_diagonal]
    exact congrArg (fun τ => τ i j) (Instrument.pre_apply _ _ ρ r)
  · simp [actualFirst, BB84DelayedMeasurements.first, Instrument.record, Kraus.apply,
      Instrument.recordOperator, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_sigma, apply_ite, ite_mul, h]

theorem existing_first_reference {n : Nat} (θ : Fin n → BB84Basis) (e : Space)
    (ρ : Operator (jointSpace n e)) :
    (BB84DelayedMeasurements.first θ e).toKraus.apply
      (((original n θ).amplify e).toKraus.apply ρ) =
      (referenceFirst θ e).record.toKraus.apply ρ :=
  (actual_delayed_first θ e ρ).symm.trans (actual_reference θ e ρ)

end
end Foundation.Quantum.QKD.BB84PairwiseReference
