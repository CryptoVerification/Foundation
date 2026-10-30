import Foundation.Crypto.Semantics.Probability.IntegerKernelCycles
import Foundation.Crypto.Semantics.Probability.FiniteFairKernelCertificate

/-! Compile certified local integer table edits to finitely fair kernels.
The final global marginal law follows from the initial certificate and four
local inequalities per move. Reversing a table edit is not a reverse sampler. -/
namespace Foundation.Probability.FairCycleKernel
open scoped BigOperators
open IntegerKernelCycles
noncomputable section
variable {A : Type} [Fintype A] [DecidableEq A] {m : Nat}

def kernel {source : A → Nat} {target : Fin m → Nat} {table : A → Fin m → ℤ} (n : Nat)
    (certificate : Certificate source target (2 ^ n) table) : A → PMF (Fin m) :=
  FiniteFairKernelCertificate.kernel n (natural table) certificate.natural_rows

omit [DecidableEq A] in
theorem kernel_real {source : A → Nat} {target : Fin m → Nat} {table : A → Fin m → ℤ} (n : Nat)
    (certificate : Certificate source target (2 ^ n) table) (a : A) (b : Fin m) :
    (kernel n certificate a b).toReal = (table a b : ℝ) / (2 ^ n : Nat) := by
  change (FiniteFairKernelCertificate.kernel n (natural table) certificate.natural_rows a b).toReal = _
  rw [FiniteFairKernelCertificate.kernel_real]
  have cast : (natural table a b : ℝ) = (table a b : ℝ) := by
    exact_mod_cast certificate.natural_cast a b
  rw [cast]

omit [DecidableEq A] in
theorem distance_eq {source : A → Nat} {target : Fin m → Nat}
    {before after : A → Fin m → ℤ} (n : Nat)
    (first : Certificate source target (2 ^ n) before)
    (last : Certificate source target (2 ^ n) after) (p : PMF A) :
    FiniteKernelVariation.distance p (kernel n first) (kernel n last) =
      ∑ a, (p a).toReal * ((∑ b, |(before a b : ℝ) - (after a b : ℝ)|) / (2 ^ n : Nat) / 2) := by
  unfold FiniteKernelVariation.distance finiteVariation
  simp_rw [kernel_real,← sub_div,abs_div,abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 ^ n : Nat)),← Finset.sum_div]

omit [DecidableEq A] in
theorem realizable {source : A → Nat} {target : Fin m → Nat} {table : A → Fin m → ℤ} (n : Nat)
    (certificate : Certificate source target (2 ^ n) table) (a : A) :
    FiniteFairSampling.Realizable n (kernel n certificate a) :=
  FiniteFairKernelCertificate.realizable n (natural table) certificate.natural_rows a

omit [DecidableEq A] in
theorem preserve {source : A → Nat} {target : Fin m → Nat} {table : A → Fin m → ℤ} (n D : Nat)
    (positive : 0 < D) (certificate : Certificate source target (2 ^ n) table)
    (p : PMF A) (q : PMF (Fin m))
    (sourceMass : ∀ a, (p a).toReal = (source a : ℝ) / D)
    (targetMass : ∀ b, (q b).toReal = (target b : ℝ) / D) : p.bind (kernel n certificate) = q :=
  FiniteFairKernelCertificate.preserve n D positive p q source target (natural table)
    certificate.natural_rows sourceMass targetMass certificate.natural_columns

def pathKernel {source : A → Nat} {target : Fin m → Nat} {before after : A → Fin m → ℤ} (n : Nat)
    (certificate : Certificate source target (2 ^ n) before) (path : Path source before after) : A → PMF (Fin m) :=
  kernel n (path.sound certificate)

theorem path_realizable {source : A → Nat} {target : Fin m → Nat} {before after : A → Fin m → ℤ} (n : Nat)
    (certificate : Certificate source target (2 ^ n) before) (path : Path source before after) (a : A) :
    FiniteFairSampling.Realizable n (pathKernel n certificate path a) := realizable n (path.sound certificate) a

theorem path_preserves {source : A → Nat} {target : Fin m → Nat} {before after : A → Fin m → ℤ} (n D : Nat)
    (positive : 0 < D) (certificate : Certificate source target (2 ^ n) before) (path : Path source before after)
    (p : PMF A) (q : PMF (Fin m))
    (sourceMass : ∀ a, (p a).toReal = (source a : ℝ) / D)
    (targetMass : ∀ b, (q b).toReal = (target b : ℝ) / D) : p.bind (pathKernel n certificate path) = q :=
  preserve n D positive (path.sound certificate) p q sourceMass targetMass

end
end Foundation.Probability.FairCycleKernel
