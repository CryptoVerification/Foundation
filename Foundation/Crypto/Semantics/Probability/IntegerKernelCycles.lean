import Foundation.Crypto.Semantics.Probability.Facts

/-! Local integer adjustments conserve row sums and source-weighted columns.
Only four corner nonnegativity obligations are needed to preserve a valid
nonnegative table. No completeness or connectivity of these moves is assumed. -/
namespace Foundation.Probability.IntegerKernelCycles
open scoped BigOperators
variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def rowWeight (source : A → Nat) (i j a : A) : ℤ :=
  (if a = i then (source j : ℤ) else 0) - (if a = j then (source i : ℤ) else 0)
def direction (k l b : B) : ℤ := (if b = k then 1 else 0) - (if b = l then 1 else 0)
def cycle (source : A → Nat) (i j : A) (k l : B) (coefficient : ℤ) (a : A) (b : B) : ℤ :=
  coefficient * rowWeight source i j a * direction k l b

def applyCycle (source : A → Nat) (table : A → B → ℤ) (i j : A) (k l : B) (coefficient : ℤ) : A → B → ℤ :=
  fun a b => table a b + cycle source i j k l coefficient a b

theorem direction_sum (k l : B) : ∑ b, direction k l b = 0 := by
  simp [direction,Finset.sum_sub_distrib]

theorem weighted_row_sum (source : A → Nat) (i j : A) : ∑ a, (source a : ℤ) * rowWeight source i j a = 0 := by
  simp only [rowWeight,mul_sub,mul_ite,mul_zero,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  ring

omit [Fintype A] in
theorem cycle_rows (source : A → Nat) (i j : A) (k l : B) (z : ℤ) (a : A) :
    ∑ b, cycle source i j k l z a b = 0 := by
  unfold cycle
  rw [← Finset.mul_sum,direction_sum,mul_zero]

omit [Fintype B] in
theorem cycle_columns (source : A → Nat) (i j : A) (k l : B) (z : ℤ) (b : B) :
    ∑ a, (source a : ℤ) * cycle source i j k l z a b = 0 := by
  calc
    _ = (∑ a, (source a : ℤ) * rowWeight source i j a) * (z * direction k l b) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      unfold cycle
      ring
    _ = 0 := by rw [weighted_row_sum,zero_mul]

omit [Fintype A] [Fintype B] in
theorem unchanged_row (source : A → Nat) (table : A → B → ℤ) (i j a : A) (k l b : B) (z : ℤ)
    (hi : a ≠ i) (hj : a ≠ j) : applyCycle source table i j k l z a b = table a b := by
  simp [applyCycle,cycle,rowWeight,hi,hj]

omit [Fintype A] [Fintype B] in
theorem unchanged_column (source : A → Nat) (table : A → B → ℤ) (i j a : A) (k l b : B) (z : ℤ)
    (hk : b ≠ k) (hl : b ≠ l) : applyCycle source table i j k l z a b = table a b := by
  simp [applyCycle,cycle,direction,hk,hl]

structure Certificate (source : A → Nat) (target : B → Nat) (N : Nat) (table : A → B → ℤ) : Prop where
  nonnegative : ∀ a b, 0 ≤ table a b
  rows : ∀ a, ∑ b, table a b = (N : ℤ)
  columns : ∀ b, ∑ a, (source a : ℤ) * table a b = (target b : ℤ) * N

omit [Fintype A] [Fintype B] in
theorem nonnegative_of_corners (source : A → Nat) (table : A → B → ℤ) (i j : A) (k l : B) (z : ℤ)
    (old : ∀ a b, 0 ≤ table a b)
    (h00 : 0 ≤ applyCycle source table i j k l z i k) (h01 : 0 ≤ applyCycle source table i j k l z i l)
    (h10 : 0 ≤ applyCycle source table i j k l z j k) (h11 : 0 ≤ applyCycle source table i j k l z j l) :
    ∀ a b, 0 ≤ applyCycle source table i j k l z a b := by
  intro a b
  by_cases rows : a = i ∨ a = j
  · by_cases cols : b = k ∨ b = l
    · rcases rows with rfl | rfl <;> rcases cols with rfl | rfl <;> assumption
    · rw [unchanged_column source table i j a k l b z (fun h => cols (Or.inl h)) (fun h => cols (Or.inr h))]
      exact old a b
  · rw [unchanged_row source table i j a k l b z (fun h => rows (Or.inl h)) (fun h => rows (Or.inr h))]
    exact old a b

theorem Certificate.adjust {source : A → Nat} {target : B → Nat} {N : Nat} {table : A → B → ℤ}
    (certificate : Certificate source target N table) (i j : A) (k l : B) (z : ℤ)
    (h00 : 0 ≤ applyCycle source table i j k l z i k) (h01 : 0 ≤ applyCycle source table i j k l z i l)
    (h10 : 0 ≤ applyCycle source table i j k l z j k) (h11 : 0 ≤ applyCycle source table i j k l z j l) :
    Certificate source target N (applyCycle source table i j k l z) where
  nonnegative := nonnegative_of_corners source table i j k l z certificate.nonnegative h00 h01 h10 h11
  rows a := by
    simp only [applyCycle,Finset.sum_add_distrib,certificate.rows,cycle_rows,add_zero]
  columns b := by
    simp only [applyCycle,mul_add,Finset.sum_add_distrib,certificate.columns,cycle_columns,add_zero]

structure Move (source : A → Nat) (before after : A → B → ℤ) where
  i : A
  j : A
  k : B
  l : B
  coefficient : ℤ
  equation : after = applyCycle source before i j k l coefficient
  corner00 : 0 ≤ after i k
  corner01 : 0 ≤ after i l
  corner10 : 0 ≤ after j k
  corner11 : 0 ≤ after j l

theorem Move.sound {source : A → Nat} {target : B → Nat} {N : Nat} {before after : A → B → ℤ}
    (move : Move source before after) (certificate : Certificate source target N before) : Certificate source target N after := by
  rw [move.equation]
  exact certificate.adjust move.i move.j move.k move.l move.coefficient
    (by simpa only [move.equation] using move.corner00) (by simpa only [move.equation] using move.corner01)
    (by simpa only [move.equation] using move.corner10) (by simpa only [move.equation] using move.corner11)

inductive Path (source : A → Nat) : (A → B → ℤ) → (A → B → ℤ) → Type where
  | refl (table) : Path source table table
  | step {before after} : Move source before after → Path source before after
  | trans {first middle last} : Path source first middle → Path source middle last → Path source first last

theorem Path.sound {source : A → Nat} {target : B → Nat} {N : Nat} {before after : A → B → ℤ}
    (path : Path source before after) (certificate : Certificate source target N before) : Certificate source target N after := by
  induction path with
  | refl => exact certificate
  | step move => exact move.sound certificate
  | trans first second ihf ihs => exact ihs (ihf certificate)

def natural (table : A → B → ℤ) : A → B → Nat := fun a b => (table a b).toNat

omit [DecidableEq A] [DecidableEq B] in
theorem Certificate.natural_cast {source : A → Nat} {target : B → Nat} {N : Nat} {table : A → B → ℤ}
    (certificate : Certificate source target N table) (a : A) (b : B) :
    (natural table a b : ℤ) = table a b := Int.toNat_of_nonneg (certificate.nonnegative a b)

omit [DecidableEq A] [DecidableEq B] in
theorem Certificate.natural_rows {source : A → Nat} {target : B → Nat} {N : Nat} {table : A → B → ℤ}
    (certificate : Certificate source target N table) : ∀ a, ∑ b, natural table a b = N := by
  intro a
  have cast : ((∑ b, natural table a b : Nat) : ℤ) = N := by
    push_cast
    simp_rw [certificate.natural_cast]
    exact certificate.rows a
  exact_mod_cast cast

omit [DecidableEq A] [DecidableEq B] in
theorem Certificate.natural_columns {source : A → Nat} {target : B → Nat} {N : Nat} {table : A → B → ℤ}
    (certificate : Certificate source target N table) : ∀ b, ∑ a, source a * natural table a b = target b * N := by
  intro b
  have cast : ((∑ a, source a * natural table a b : Nat) : ℤ) = (target b : ℤ) * N := by
    push_cast
    simp_rw [certificate.natural_cast]
    exact certificate.columns b
  exact_mod_cast cast

def signed (counts : A → B → Nat) : A → B → ℤ := fun a b => counts a b

omit [DecidableEq A] [DecidableEq B] in
theorem Certificate.ofNat (source : A → Nat) (target : B → Nat) (N : Nat) (counts : A → B → Nat)
    (rows : ∀ a, ∑ b, counts a b = N) (columns : ∀ b, ∑ a, source a * counts a b = target b * N) :
    Certificate source target N (signed counts) where
  nonnegative _ _ := by simp [signed]
  rows a := by
    change (∑ b, (counts a b : ℤ)) = (N : ℤ)
    exact_mod_cast rows a
  columns b := by
    change (∑ a, (source a : ℤ) * (counts a b : ℤ)) = (target b : ℤ) * (N : ℤ)
    exact_mod_cast columns b

omit [Fintype A] [Fintype B] in
theorem applyCycle_neg (source : A → Nat) (table : A → B → ℤ) (i j : A) (k l : B) (z : ℤ) :
    applyCycle source (applyCycle source table i j k l z) i j k l (-z) = table := by
  funext a b
  simp only [applyCycle,cycle]
  ring

def Move.reverse {source : A → Nat} {before after : A → B → ℤ} (move : Move source before after)
    (nonnegative : ∀ a b, 0 ≤ before a b) : Move source after before where
  i := move.i
  j := move.j
  k := move.k
  l := move.l
  coefficient := -move.coefficient
  equation := by
    have changed := congrArg (fun table => applyCycle source table move.i move.j move.k move.l (-move.coefficient)) move.equation
    exact (changed.trans (applyCycle_neg source before move.i move.j move.k move.l move.coefficient)).symm
  corner00 := nonnegative _ _
  corner01 := nonnegative _ _
  corner10 := nonnegative _ _
  corner11 := nonnegative _ _

def Path.reverse {source : A → Nat} {target : B → Nat} {N : Nat} {before after : A → B → ℤ}
    (path : Path source before after) (certificate : Certificate source target N before) : Path source after before :=
  match path with
  | .refl table => .refl table
  | .step move => .step (move.reverse certificate.nonnegative)
  | .trans first second => .trans (second.reverse (first.sound certificate)) (first.reverse certificate)

end Foundation.Probability.IntegerKernelCycles
