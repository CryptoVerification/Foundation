import Foundation.Crypto.Semantics.Probability.ClassicalBitDyadicSampler
import Foundation.Crypto.Semantics.Probability.FiniteFairSampling
import Foundation.Crypto.Semantics.Probability.FiniteKernelVariation

/-! Integer row/column certificates for finite fair conditional kernels.
Row sums specify fair seeds; source-weighted column sums certify the endpoint
law. No machine runtime or optimality follows from these semantic certificates. -/
namespace Foundation.Probability.FiniteFairKernelCertificate
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators ENNReal
noncomputable section

def kernel {A : Type} {m : Nat} (n : Nat) (counts : A → Fin m → Nat)
    (normal : ∀ a, ∑ b, counts a b = 2 ^ n) (a : A) : PMF (Fin m) :=
  PMF.ofFintype (fun b => ENNReal.ofReal ((counts a b : ℝ) / (2 ^ n : Nat))) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => by positivity),← Finset.sum_div,← Nat.cast_sum,normal a]
    rw [div_self (by positivity : ((2 ^ n : Nat) : ℝ) ≠ 0),ENNReal.ofReal_one])

theorem kernel_real {A : Type} {m : Nat} (n : Nat) (counts : A → Fin m → Nat)
    (normal : ∀ a, ∑ b, counts a b = 2 ^ n) (a : A) (b : Fin m) :
    (kernel n counts normal a b).toReal = (counts a b : ℝ) / (2 ^ n : Nat) :=
  ENNReal.toReal_ofReal (by positivity)

def sample {A : Type} {m : Nat} (n : Nat) (counts : A → Fin m → Nat)
    (normal : ∀ a, ∑ b, counts a b = 2 ^ n) (a : A) : Fin (2 ^ n) → Fin m :=
  sampleCounts (counts a) (normal a)

theorem sample_law {A : Type} {m : Nat} (n : Nat) (counts : A → Fin m → Nat)
    (normal : ∀ a, ∑ b, counts a b = 2 ^ n) (a : A) :
    (uniform (Fin (2 ^ n))).map (sample n counts normal a) = kernel n counts normal a := by
  ext b
  apply (ENNReal.toReal_eq_toReal_iff' (((uniform (Fin (2 ^ n))).map _).apply_ne_top b)
    ((kernel n counts normal a).apply_ne_top b)).mp
  rw [← FiniteKernelVariation.singleton,eventProb_map,sample,sampleCounts_event_probability,
    ENNReal.toReal_div,kernel_real]
  simp

theorem realizable {A : Type} {m : Nat} (n : Nat) (counts : A → Fin m → Nat)
    (normal : ∀ a, ∑ b, counts a b = 2 ^ n) (a : A) :
    FiniteFairSampling.Realizable n (kernel n counts normal a) :=
  ⟨sample n counts normal a,sample_law n counts normal a⟩

theorem bits_law {A : Type} {m : Nat} (n : Nat) (counts : A → Fin m → Nat)
    (normal : ∀ a, ∑ b, counts a b = 2 ^ n) (a : A) :
    (uniform (Fin n → Bool)).map (sample n counts normal a ∘ bitIndexEquiv n) = kernel n counts normal a := by
  rw [← PMF.map_comp,uniform_map_equiv]
  exact sample_law n counts normal a

theorem preserve {A : Type} [Fintype A] {m : Nat} (n D : Nat) (positive : 0 < D)
    (p : PMF A) (q : PMF (Fin m)) (source : A → Nat) (target : Fin m → Nat)
    (counts : A → Fin m → Nat) (normal : ∀ a, ∑ b, counts a b = 2 ^ n)
    (sourceMass : ∀ a, (p a).toReal = (source a : ℝ) / D)
    (targetMass : ∀ b, (q b).toReal = (target b : ℝ) / D)
    (columns : ∀ b, ∑ a, source a * counts a b = target b * 2 ^ n) :
    p.bind (kernel n counts normal) = q := by
  ext b
  apply (ENNReal.toReal_eq_toReal_iff' ((_ : PMF (Fin m)).apply_ne_top b) (q.apply_ne_top b)).mp
  rw [FiniteKernelVariation.bind_real,targetMass]
  simp_rw [sourceMass,kernel_real]
  have term (a : A) : (source a : ℝ) / D * ((counts a b : ℝ) / (2 ^ n : Nat)) =
      ((source a * counts a b : Nat) : ℝ) / ((D : ℝ) * (2 ^ n : Nat)) := by
    push_cast
    ring
  simp_rw [term]
  rw [← Finset.sum_div,← Nat.cast_sum,columns b]
  push_cast
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt positive
  have hn : ((2 ^ n : Nat) : ℝ) ≠ 0 := by positivity
  field_simp

theorem columns_of_preserve {A : Type} [Fintype A] {m : Nat} (n D : Nat) (positive : 0 < D)
    (p : PMF A) (q : PMF (Fin m)) (source : A → Nat) (target : Fin m → Nat)
    (counts : A → Fin m → Nat) (normal : ∀ a, ∑ b, counts a b = 2 ^ n)
    (sourceMass : ∀ a, (p a).toReal = (source a : ℝ) / D)
    (targetMass : ∀ b, (q b).toReal = (target b : ℝ) / D)
    (preserve : p.bind (kernel n counts normal) = q) :
    ∀ b, ∑ a, source a * counts a b = target b * 2 ^ n := by
  intro b
  have h := congrArg (fun law : PMF (Fin m) => (law b).toReal) preserve
  rw [FiniteKernelVariation.bind_real,targetMass] at h
  simp_rw [sourceMass,kernel_real] at h
  have term (a : A) : (source a : ℝ) / D * ((counts a b : ℝ) / (2 ^ n : Nat)) =
      ((source a * counts a b : Nat) : ℝ) / ((D : ℝ) * (2 ^ n : Nat)) := by
    push_cast
    ring
  simp_rw [term] at h
  rw [← Finset.sum_div,← Nat.cast_sum] at h
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt positive
  have hn : ((2 ^ n : Nat) : ℝ) ≠ 0 := by positivity
  have cross := (div_eq_div_iff (mul_ne_zero hd hn) hd).mp h
  have scaled : (((∑ a, source a * counts a b : Nat) : ℝ) - (target b : ℝ) * (2 ^ n : Nat)) * D = 0 := by
    nlinarith [cross]
  have equal := sub_eq_zero.mp ((mul_eq_zero.mp scaled).resolve_right hd)
  exact_mod_cast equal

def independentCounts {A : Type} {m : Nat} (target : Fin m → Nat) (extra : Nat) : A → Fin m → Nat :=
  fun _ b => target b * 2 ^ extra

theorem independent_rows {A : Type} {m : Nat} (target : Fin m → Nat) (d extra : Nat)
    (total : ∑ b, target b = 2 ^ d) : ∀ a : A, ∑ b, independentCounts target extra a b = 2 ^ (d + extra) := by
  intro a
  simp only [independentCounts,← Finset.sum_mul,total,pow_add]

theorem independent_columns {A : Type} [Fintype A] {m : Nat} (source : A → Nat) (target : Fin m → Nat)
    (d extra : Nat) (total : ∑ a, source a = 2 ^ d) :
    ∀ b, ∑ a, source a * independentCounts target extra a b = target b * 2 ^ (d + extra) := by
  intro b
  simp only [independentCounts,← mul_assoc,← Finset.sum_mul,total,pow_add]
  ring

end
end Foundation.Probability.FiniteFairKernelCertificate
