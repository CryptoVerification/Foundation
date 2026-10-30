import Foundation.Crypto.Semantics.Probability.FairCycleKernel

/-! Local admissibility of four affected pairs preserves an arbitrary
relation on kernel support. This can retain ciphertext, labels or interface
invariants without supplying a new global joint-distribution equality. -/
namespace Foundation.Probability.IntegerKernelCycles
variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

omit [Fintype A] [Fintype B] in
theorem relation_of_corners (source : A → Nat) (table : A → B → ℤ) (i j : A) (k l : B) (z : ℤ)
    (relation : A → B → Prop) (old : ∀ a b, table a b ≠ 0 → relation a b)
    (h00 : relation i k) (h01 : relation i l) (h10 : relation j k) (h11 : relation j l) :
    ∀ a b, applyCycle source table i j k l z a b ≠ 0 → relation a b := by
  intro a b used
  by_cases rows : a = i ∨ a = j
  · by_cases cols : b = k ∨ b = l
    · rcases rows with rfl | rfl <;> rcases cols with rfl | rfl <;> assumption
    · rw [unchanged_column source table i j a k l b z (fun h => cols (Or.inl h)) (fun h => cols (Or.inr h))] at used
      exact old a b used
  · rw [unchanged_row source table i j a k l b z (fun h => rows (Or.inl h)) (fun h => rows (Or.inr h))] at used
    exact old a b used

def Respects (relation : A → B → Prop) {source : A → Nat} {before after : A → B → ℤ}
    (path : Path source before after) : Prop :=
  match path with
  | .refl _ => True
  | .step move => relation move.i move.k ∧ relation move.i move.l ∧ relation move.j move.k ∧ relation move.j move.l
  | .trans first second => Respects relation first ∧ Respects relation second

omit [Fintype A] [Fintype B] in
theorem Path.relation {source : A → Nat} {before after : A → B → ℤ} (path : Path source before after)
    (relation : A → B → Prop) (old : ∀ a b, before a b ≠ 0 → relation a b) (compatible : Respects relation path) :
    ∀ a b, after a b ≠ 0 → relation a b := by
  induction path with
  | refl => exact old
  | step move =>
    rw [move.equation]
    exact relation_of_corners source _ move.i move.j move.k move.l move.coefficient relation old
      compatible.1 compatible.2.1 compatible.2.2.1 compatible.2.2.2
  | trans first second ihf ihs => exact ihs (ihf old compatible.1) compatible.2

end Foundation.Probability.IntegerKernelCycles

namespace Foundation.Probability.FairCycleKernel
open IntegerKernelCycles
variable {A : Type} [Fintype A] [DecidableEq A] {m : Nat}

omit [DecidableEq A] in
theorem support_table_nonzero {source : A → Nat} {target : Fin m → Nat} {table : A → Fin m → ℤ} (n : Nat)
    (certificate : Certificate source target (2 ^ n) table) (a : A) (b : Fin m)
    (supported : b ∈ (kernel n certificate a).support) : table a b ≠ 0 := by
  intro zero
  have real : (kernel n certificate a b).toReal = 0 := by
    change (FiniteFairKernelCertificate.kernel n (natural table) certificate.natural_rows a b).toReal = _
    rw [FiniteFairKernelCertificate.kernel_real]
    simp [natural,zero]
  have probability : kernel n certificate a b = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp real).resolve_right ((kernel n certificate a).apply_ne_top b)
  exact (PMF.mem_support_iff _ _).mp supported probability

omit [DecidableEq A] in
theorem support_iff_table_nonzero {source : A → Nat} {target : Fin m → Nat} {table : A → Fin m → ℤ} (n : Nat)
    (certificate : Certificate source target (2 ^ n) table) (a : A) (b : Fin m) :
    b ∈ (kernel n certificate a).support ↔ table a b ≠ 0 := by
  constructor
  · exact support_table_nonzero n certificate a b
  · intro nonzero
    apply (PMF.mem_support_iff _ _).mpr
    intro probability
    have real := congrArg ENNReal.toReal probability
    change (FiniteFairKernelCertificate.kernel n (natural table) certificate.natural_rows a b).toReal = 0 at real
    rw [FiniteFairKernelCertificate.kernel_real] at real
    have numerator := (div_eq_zero_iff.mp real).resolve_right (by positivity : ((2 ^ n : Nat) : ℝ) ≠ 0)
    have naturalZero : natural table a b = 0 := by exact_mod_cast numerator
    have tableZero : table a b = 0 := by rw [← certificate.natural_cast a b,naturalZero]; rfl
    exact nonzero tableZero


/- The retained label can have an arbitrary (including infinite) type. -/
theorem path_joint_preserves {C : Type} {source : A → Nat} {target : Fin m → Nat}
    {before after : A → Fin m → ℤ} (n D : Nat) (positive : 0 < D)
    (certificate : Certificate source target (2 ^ n) before) (path : Path source before after)
    (p : PMF A) (q : PMF (Fin m))
    (sourceMass : ∀ a, (p a).toReal = (source a : ℝ) / D)
    (targetMass : ∀ b, (q b).toReal = (target b : ℝ) / D)
    (inputLabel : A → C) (outputLabel : Fin m → C)
    (old : ∀ a b, before a b ≠ 0 → outputLabel b = inputLabel a)
    (compatible : Respects (fun a b => outputLabel b = inputLabel a) path) :
    (p.map (fun a => (a,inputLabel a))).bind (fun original =>
      (pathKernel n certificate path original.1).map (fun final => (final,original.2))) =
      q.map (fun b => (b,outputLabel b)) := by
  rw [PMF.bind_map]
  simp only [Function.comp_def]
  have each (a : A) : (pathKernel n certificate path a).map (fun b => (b,inputLabel a)) =
      (pathKernel n certificate path a).map (fun b => (b,outputLabel b)) := by
    change (pathKernel n certificate path a).bind _ = (pathKernel n certificate path a).bind _
    apply bind_congr_of_support
    intro b supported
    have nonzero := support_table_nonzero n (path.sound certificate) a b supported
    have label := path.relation _ old compatible a b nonzero
    simp only [Function.comp_def]
    rw [label]
  simp_rw [each]
  rw [← PMF.map_bind,path_preserves n D positive certificate path p q sourceMass targetMass]

end Foundation.Probability.FairCycleKernel
