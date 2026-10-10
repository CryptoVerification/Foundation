import Foundation.Quantum.Instrument
import Foundation.Quantum.Distinguishability

/-! Instruments compose with physical channels and retain arbitrary auxiliary
systems. Completeness is derived from the Kraus effects. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Kraus
variable {a b c : Space}

theorem seq_effect (K : Kraus a b) (L : Kraus b c) :
    (K.seq L).effect = K.dual L.effect := by
  simp only [seq, effect, dual, Fintype.sum_prod_type, Matrix.conjTranspose_mul]
  simp_rw [Matrix.mul_assoc, ← Matrix.mul_assoc (L.operator _).conjTranspose,
    ← Matrix.mul_sum, ← Matrix.sum_mul]

/-- The Heisenberg action commutes with finite sums. -/
theorem dual_sum {ι : Type*} (K : Kraus a b) (s : Finset ι) (f : ι → Operator b) :
    K.dual (∑ i ∈ s, f i) = ∑ i ∈ s, K.dual (f i) := by
  simp only [dual, Matrix.mul_sum, Matrix.sum_mul]
  rw [Finset.sum_comm]

end Kraus

namespace Instrument
variable {a b c : Space} {n : Nat}

/-- First run the channel, then keep the instrument's physical outcome. -/
def pre (I : Instrument b c n) (C : Channel a b) : Instrument a c n where
  branch r := C.toKraus.seq (I.branch r)
  complete := by
    simp only [Kraus.seq_effect]
    rw [← Kraus.dual_sum, I.complete, Kraus.dual_one, C.complete]

theorem pre_apply (I : Instrument b c n) (C : Channel a b) (ρ : Operator a) (r : Fin n) :
    ((I.pre C).branch r).apply ρ = (I.branch r).apply (C.toKraus.apply ρ) :=
  C.toKraus.seq_apply (I.branch r) ρ

theorem pre_probability (I : Instrument b c n) (C : Channel a b) (ρ : Density a) (r : Fin n) :
    (I.pre C).probability ρ r = I.probability (C.run ρ) r := by
  unfold probability
  rw [pre_apply]
  rfl

/-- The same branch acts locally and retains the entire auxiliary subsystem. -/
def amplify (I : Instrument a b n) (e : Space) :
    Instrument (.tensor a e) (.tensor b e) n where
  branch r := (I.branch r).amplify e
  complete := by
    simp only [Kraus.amplify_effect]
    have he : (∑ r, Op.tensor (I.branch r).effect (Op.ident e)) =
        Op.tensor (∑ r, (I.branch r).effect) (Op.ident e) := by
      ext i j
      simp [Op.tensor, Matrix.kronecker, Matrix.kroneckerMap, Matrix.sum_apply, Finset.sum_mul]
    rw [he, I.complete]
    exact Matrix.one_kronecker_one

theorem amplify_pre_apply (I : Instrument b c n) (C : Channel a b) (e : Space)
    (ρ : Operator (.tensor a e)) (r : Fin n) :
    (((I.pre C).amplify e).branch r).apply ρ =
      ((I.amplify e).branch r).apply ((C.amplify e).toKraus.apply ρ) := by
  change ((C.toKraus.seq (I.branch r)).amplify e).apply ρ = _
  rw [Kraus.amplify_seq, Kraus.seq_apply]
  rfl

/-- A branch trace equals its effect's acceptance weight, including trace-decreasing branches. -/
theorem branch_trace (I : Instrument a b n) (ρ : Operator a) (r : Fin n) :
    ((I.branch r).apply ρ).trace = ((I.branch r).effect * ρ).trace := by
  simpa only [Matrix.one_mul, Kraus.dual_one] using (I.branch r).trace_dual ρ 1

end Instrument
end
end Foundation.Quantum
