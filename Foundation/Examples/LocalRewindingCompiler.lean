import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Algebra of a generated two-stage rewinding proposal.

The continuation's challenge-class masses determine its proposal. The finite
sum normalization and the pointwise balance are checked here. Executable
sampling, regenerative stopping semantics, and the complete Schnorr output
law are separate obligations; this is not a generic ZK compiler theorem.
-/

namespace Foundation.Examples.LocalRewindingCompiler

open scoped BigOperators

variable {X Y C : Type*} [Fintype X] [Fintype Y] [Fintype C] [DecidableEq C]

def classMass (law : Y → ℚ) (challenge : X → Y → C) (x : X) (c : C) : ℚ :=
  ∑ y, if challenge x y = c then law y else 0

omit [Fintype X] in
theorem class_mass_sum (law : Y → ℚ) (challenge : X → Y → C) (x : X) :
    ∑ c, classMass law challenge x c = ∑ y, law y := by
  unfold classMass
  rw [Finset.sum_comm]
  simp

omit [Fintype X] [Fintype C] in
theorem actual_class_positive (law : Y → ℚ) (challenge : X → Y → C)
    (nonnegative : ∀ y, 0 ≤ law y) (x : X) (y : Y) (positive : 0 < law y) :
    0 < classMass law challenge x (challenge x y) := by
  have single : law y ≤ classMass law challenge x (challenge x y) := by
    unfold classMass
    have bound := Finset.single_le_sum
      (f := fun z => if challenge x z = challenge x y then law z else 0)
      (fun z (_ : z ∈ Finset.univ) => by split_ifs <;> simp [nonnegative])
      (Finset.mem_univ y)
    simpa using bound
  exact positive.trans_le single

def retryDenominator (p mass : ℚ) : ℚ := 1 - (1 - p) * mass

theorem denominator_lower (p mass : ℚ) (pUpper : p ≤ 1) (massUpper : mass ≤ 1) :
    p ≤ retryDenominator p mass := by
  have product := mul_nonneg (sub_nonneg.mpr pUpper) (sub_nonneg.mpr massUpper)
  dsimp [retryDenominator]
  nlinarith

def rowWeight (mass : X → C → ℚ) (p : ℚ) (x : X) : ℚ :=
  ∑ c, if mass x c = 0 then 0 else retryDenominator p (mass x c)

def guessProposal (mass : X → C → ℚ) (p : ℚ) (x : X) (c : C) : ℚ :=
  (if mass x c = 0 then 0 else retryDenominator p (mass x c)) / rowWeight mass p x

omit [Fintype X] [DecidableEq C] in
theorem guess_proposal_normalized (mass : X → C → ℚ) (p : ℚ) (x : X)
    (nonzero : rowWeight mass p x ≠ 0) : ∑ c, guessProposal mass p x c = 1 := by
  simp only [guessProposal, ← Finset.sum_div]
  exact div_self nonzero

def localExit (law : Y → ℚ) (challenge : X → Y → C)
    (mass : X → C → ℚ) (p : ℚ) (x : X) (c : C) (y : Y) : ℚ :=
  if challenge x y = c then law y * p / retryDenominator p (mass x c) else 0

omit [Fintype X] [Fintype Y] in
/-- The generated guess distribution cancels the class-dependent restart
factor. No global output coupling is an input to this identity. -/
theorem generated_row_exit (law : Y → ℚ) (challenge : X → Y → C)
    (mass : X → C → ℚ) (p : ℚ) (x : X) (y : Y)
    (productive : mass x (challenge x y) ≠ 0)
    (denominatorNonzero : retryDenominator p (mass x (challenge x y)) ≠ 0)
    (rowNonzero : rowWeight mass p x ≠ 0) :
    (∑ c, guessProposal mass p x c * localExit law challenge mass p x c y) =
      law y * p / rowWeight mass p x := by
  rw [Finset.sum_eq_single (challenge x y)]
  · simp [guessProposal, localExit, productive]
    field_simp
  · intro c _ distinct
    have different : challenge x y ≠ c := Ne.symm distinct
    simp [localExit, different]
  · simp

def totalWeight (contextLaw : X → ℚ) (mass : X → C → ℚ) (p : ℚ) : ℚ :=
  ∑ x, contextLaw x * rowWeight mass p x

def contextProposal (contextLaw : X → ℚ) (mass : X → C → ℚ)
    (p : ℚ) (x : X) : ℚ :=
  contextLaw x * rowWeight mass p x / totalWeight contextLaw mass p

omit [DecidableEq C] in
theorem context_proposal_normalized (contextLaw : X → ℚ) (mass : X → C → ℚ)
    (p : ℚ) (nonzero : totalWeight contextLaw mass p ≠ 0) :
    ∑ x, contextProposal contextLaw mass p x = 1 := by
  simp only [contextProposal, ← Finset.sum_div]
  exact div_self nonzero

omit [Fintype Y] [DecidableEq C] in
theorem generated_joint_balance (contextLaw : X → ℚ) (law : Y → ℚ)
    (mass : X → C → ℚ) (p : ℚ) (x : X) (y : Y)
    (rowNonzero : rowWeight mass p x ≠ 0)
    (totalNonzero : totalWeight contextLaw mass p ≠ 0) :
    contextProposal contextLaw mass p x * (law y * p / rowWeight mass p x) =
      contextLaw x * law y * (p / totalWeight contextLaw mass p) := by
  unfold contextProposal
  field_simp

omit [Fintype Y] [DecidableEq C] in
theorem generated_output_law (contextLaw : X → ℚ) (law : Y → ℚ)
    (mass : X → C → ℚ) (p : ℚ) (x : X) (y : Y)
    (rowNonzero : rowWeight mass p x ≠ 0)
    (totalNonzero : totalWeight contextLaw mass p ≠ 0) (pNonzero : p ≠ 0) :
    (contextProposal contextLaw mass p x * (law y * p / rowWeight mass p x)) /
      (p / totalWeight contextLaw mass p) = contextLaw x * law y := by
  rw [generated_joint_balance contextLaw law mass p x y rowNonzero totalNonzero]
  exact mul_div_cancel_right₀ _ (div_ne_zero pNonzero totalNonzero)

/-- The local expected work before either acceptance or an outer restart. -/
def localWork (p mass : ℚ) : ℚ := (1 + mass) / retryDenominator p mass

omit [Fintype X] [DecidableEq C] in
theorem generated_work_cancellation (mass : X → C → ℚ) (p : ℚ) (x : X) (c : C)
    (productive : mass x c ≠ 0) (rowNonzero : rowWeight mass p x ≠ 0)
    (denominatorNonzero : retryDenominator p (mass x c) ≠ 0) :
    guessProposal mass p x c * localWork p (mass x c) =
      (1 + mass x c) / rowWeight mass p x := by
  simp only [guessProposal, localWork, if_neg productive]
  field_simp

def productiveWork (mass : X → C → ℚ) (x : X) : ℚ :=
  ∑ c, if mass x c = 0 then 0 else 1 + mass x c

def productiveClasses (mass : X → C → ℚ) (x : X) : ℚ :=
  ∑ c, if mass x c = 0 then 0 else 1

omit [Fintype X] [DecidableEq C] in
theorem productive_work_count (mass : X → C → ℚ) (x : X)
    (normalized : ∑ c, mass x c = 1) :
    productiveWork mass x = productiveClasses mass x + 1 := by
  have pointwise : ∀ c, (if mass x c = 0 then 0 else 1 + mass x c) =
      (if mass x c = 0 then 0 else 1) + mass x c := by
    intro c
    by_cases zero : mass x c = 0 <;> simp [zero]
  unfold productiveWork productiveClasses
  simp_rw [pointwise]
  rw [Finset.sum_add_distrib, normalized]

omit [Fintype X] [DecidableEq C] in
theorem generated_row_work (mass : X → C → ℚ) (p : ℚ) (x : X)
    (rowNonzero : rowWeight mass p x ≠ 0)
    (denominators : ∀ c, mass x c ≠ 0 → retryDenominator p (mass x c) ≠ 0) :
    (∑ c, guessProposal mass p x c * localWork p (mass x c)) =
      productiveWork mass x / rowWeight mass p x := by
  rw [productiveWork, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  by_cases zero : mass x c = 0
  · simp [guessProposal, zero]
  · simpa [zero] using generated_work_cancellation mass p x c zero rowNonzero
      (denominators c zero)

omit [DecidableEq C] in
theorem generated_total_work (contextLaw : X → ℚ) (mass : X → C → ℚ) (p : ℚ)
    (rowsNonzero : ∀ x, rowWeight mass p x ≠ 0)
    (totalNonzero : totalWeight contextLaw mass p ≠ 0) (pNonzero : p ≠ 0) :
    (∑ x, contextProposal contextLaw mass p x *
      (productiveWork mass x / rowWeight mass p x)) /
        (p / totalWeight contextLaw mass p) =
      (∑ x, contextLaw x * productiveWork mass x) / p := by
  have rows : ∀ x, contextProposal contextLaw mass p x *
      (productiveWork mass x / rowWeight mass p x) =
      contextLaw x * productiveWork mass x / totalWeight contextLaw mass p := by
    intro x
    unfold contextProposal
    field_simp [rowsNonzero x]
  simp_rw [rows]
  rw [← Finset.sum_div]
  field_simp

theorem unequal_class_output_zero :
    ((1 / 3 : ℚ) / (2 * (2 - 1 / 3))) /
      ((1 / 3) / (2 * (2 - 1 / 3)) + (2 / 3) / (2 * (2 - 2 / 3))) =
      2 / 7 := by norm_num

theorem unequal_class_corrected_guess :
    retryDenominator (1 / 2) (1 / 3) /
      (retryDenominator (1 / 2) (1 / 3) + retryDenominator (1 / 2) (2 / 3)) =
      5 / 9 := by norm_num [retryDenominator]

end Foundation.Examples.LocalRewindingCompiler
