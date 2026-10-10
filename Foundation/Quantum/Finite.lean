import Foundation.Quantum.Space
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Basis-chosen finite complex spaces. Matrix rows are outputs and columns
are inputs; `seq f g` means first f, then g. These are the finite-dimensional
instances of Heunen 2.6.2, 3.2.9, 3.3.4--3.3.7, not a reconstruction theorem
for arbitrary Hilbert categories. Cups are deliberately unnormalised. -/
namespace Foundation.Quantum

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Space

@[simp] theorem sum_tensor {a b : Space} (h : (a.tensor b).Basis → ℂ) :
    ∑ x, h x = ∑ i : a.Basis, ∑ j : b.Basis, h (i, j) :=
  Fintype.sum_prod_type h

end Space

abbrev Op (a b : Space) := Matrix b.Basis a.Basis ℂ

namespace Op

@[simp] theorem card_if {α : Type*} (p : Prop) [Decidable p] (s t : Finset α) :
    (if p then s else t).card = if p then s.card else t.card := by
  split <;> rfl

variable {a b c d e z : Space}

def ident (a : Space) : Op a a := 1
def seq (f : Op a b) (g : Op b c) : Op a c := g * f
def tensor (f : Op a b) (g : Op c d) : Op (.tensor a c) (.tensor b d) :=
  Matrix.kronecker f g
def dagger (f : Op a b) : Op b a := f.conjTranspose
def conjugate (f : Op a b) : Op a b := fun i j => star (f i j)

/-- A function on basis indices extends linearly; it is not a nonlinear map on states. -/
def basisMap (f : a.Basis → b.Basis) : Op a b := fun i j => if i = f j then 1 else 0

def copy (a : Space) : Op a (.tensor a a) := basisMap (fun i => (i, i))
def erase (a : Space) : Op a .unit := fun _ _ => 1
def cup (a : Space) : Op .unit (.tensor a a) := fun i _ => if i.1 = i.2 then 1 else 0
def cap (a : Space) : Op (.tensor a a) .unit := dagger (cup a)
def swap (a b : Space) : Op (.tensor a b) (.tensor b a) := basisMap Prod.swap
def assoc (a b c : Space) : Op (.tensor (.tensor a b) c) (.tensor a (.tensor b c)) :=
  basisMap (fun p => (p.1.1, p.1.2, p.2))
def unleft (a : Space) : Op (.tensor .unit a) a := basisMap Prod.snd
def unright (a : Space) : Op (.tensor a .unit) a := basisMap Prod.fst

def name (f : Op a b) : Op .unit (.tensor a b) := fun i _ => f i.2 i.1

def leftErase (a : Space) : Op (.tensor a a) a := seq (tensor (erase a) (ident a)) (unleft a)
def rightErase (a : Space) : Op (.tensor a a) a := seq (tensor (ident a) (erase a)) (unright a)

@[simp] theorem seq_ident (f : Op a b) : seq f (ident b) = f := Matrix.one_mul f
@[simp] theorem ident_seq (f : Op a b) : seq (ident a) f = f := Matrix.mul_one f
theorem seq_assoc (f : Op a b) (g : Op b c) (h : Op c d) :
    seq (seq f g) h = seq f (seq g h) := (Matrix.mul_assoc h g f).symm
@[simp] theorem dagger_dagger (f : Op a b) : dagger (dagger f) = f :=
  Matrix.conjTranspose_conjTranspose f
theorem dagger_seq (f : Op a b) (g : Op b c) :
    dagger (seq f g) = seq (dagger g) (dagger f) := Matrix.conjTranspose_mul g f
theorem tensor_seq (f : Op a b) (g : Op b c) (h : Op d e) (k : Op e z) :
    tensor (seq f g) (seq h k) = seq (tensor f h) (tensor g k) :=
  Matrix.mul_kronecker_mul g f k h

@[simp] theorem basisMap_apply (h : a.Basis → b.Basis) (i j) :
    basisMap h i j = if i = h j then 1 else 0 := rfl

@[simp] theorem leftErase_apply (a : Space) (i : a.Basis) (j : a.Basis × a.Basis) :
    leftErase a i j = if i = j.2 then 1 else 0 := by
  simp [-Finset.sum_boole, Space.Basis, leftErase, unleft, seq, tensor, erase, ident, basisMap,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]

@[simp] theorem rightErase_apply (a : Space) (i : a.Basis) (j : a.Basis × a.Basis) :
    rightErase a i j = if i = j.1 then 1 else 0 := by
  simp [-Finset.sum_boole, Space.Basis, rightErase, unright, seq, tensor, erase, ident, basisMap,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]

/-- The naming calculation (2.19) used in the proof of 3.3.9. -/
theorem correlated_cup (m : Op a b) :
    seq (cup a) (tensor (conjugate m) m) = name (seq (dagger m) m) := by
  ext i j
  change (∑ k : a.Basis × a.Basis,
    (star (m i.1 k.1) * m i.2 k.2) * (if k.1 = k.2 then 1 else 0)) =
    ∑ k : a.Basis, m i.2 k * star (m i.1 k)
  simp [Fintype.sum_prod_type, mul_comm]

/-- Heunen 3.3.6 for the chosen classical basis. -/
theorem cup_copy (a : Space) : cup a = seq (dagger (erase a)) (copy a) := by
  ext ⟨i, k⟩ j
  change (if i = k then (1 : ℂ) else 0) =
    ∑ x : a.Basis, (if (i, k) = (x, x) then (1 : ℂ) else 0) * star (1 : ℂ)
  simp only [star_one, mul_one, Prod.mk.injEq]
  by_cases h : i = k
  · subst k; simp
  · have hn : ∀ x : a.Basis, ¬ (i = x ∧ k = x) := by
      intro x hx
      exact h (hx.1.trans hx.2.symm)
    simp [-Finset.sum_boole, hn, h]

@[simp] theorem name_ident (a : Space) : name (ident a) = cup a := by
  ext i j
  simp [-Finset.sum_boole, name, ident, cup, Matrix.one_apply, eq_comm]

/-- The two classical counits in 3.3.4. -/
theorem copy_leftErase (a : Space) : seq (copy a) (leftErase a) = ident a := by
  ext i j
  simp [-Finset.sum_boole, Space.Basis, seq, copy, basisMap, Matrix.mul_apply, ident, Matrix.one_apply]

theorem copy_rightErase (a : Space) : seq (copy a) (rightErase a) = ident a := by
  ext i j
  simp [-Finset.sum_boole, Space.Basis, seq, copy, basisMap, Matrix.mul_apply, ident, Matrix.one_apply]

/-- Specialness: delta is a dagger mono (3.3.4). -/
theorem copy_special (a : Space) : seq (copy a) (dagger (copy a)) = ident a := by
  ext i j
  simp [-Finset.sum_boole, Space.Basis, seq, copy, basisMap, dagger, Matrix.mul_apply, Matrix.conjTranspose_apply,
    ident, Matrix.one_apply, Prod.mk.injEq, eq_comm]

/-- Coassociativity includes the explicit associator, rather than identifying types. -/
theorem copy_coassoc (a : Space) :
    seq (seq (copy a) (tensor (copy a) (ident a))) (assoc a a a) =
      seq (copy a) (tensor (ident a) (copy a)) := by
  ext ⟨i, j, k⟩ l
  simp [-Finset.sum_boole, ite_and, Space.Basis, seq, copy, tensor, ident, assoc, basisMap, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

theorem copy_comm (a : Space) : seq (copy a) (swap a a) = copy a := by
  ext ⟨i, j⟩ k
  simp [-Finset.sum_boole, ite_and, Space.Basis, seq, copy, swap, basisMap, Matrix.mul_apply]

/-- Frobenius equation (3.3), with the associator oriented as in the source. -/
theorem copy_frobenius (a : Space) :
    seq (dagger (copy a)) (copy a) =
      seq (seq (tensor (ident a) (copy a)) (dagger (assoc a a a)))
        (tensor (dagger (copy a)) (ident a)) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [-Finset.sum_boole, ite_and, Space.Basis, seq, copy, tensor, ident, assoc, dagger, basisMap,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- First snake equation of (2.18). -/
theorem snake_left (a : Space) :
    seq (seq (seq (dagger (unright a)) (tensor (ident a) (cup a)))
      (dagger (assoc a a a)))
      (seq (tensor (cap a) (ident a)) (unleft a)) = ident a := by
  ext i j
  simp [-Finset.sum_boole, ite_and, Space.Basis, seq, unright, unleft, tensor, cup, cap, assoc, dagger, ident, basisMap,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Prod.mk.injEq]

/-- Second snake equation of (2.18). -/
theorem snake_right (a : Space) :
    seq (seq (seq (dagger (unleft a)) (tensor (cup a) (ident a)))
      (assoc a a a))
      (seq (tensor (ident a) (cap a)) (unright a)) = ident a := by
  ext i j
  simp [-Finset.sum_boole, ite_and, Space.Basis, seq, unright, unleft, tensor, cup, cap, assoc, dagger, ident, basisMap,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Prod.mk.injEq]

/-- A fixed gate with rational complex amplitudes, creating a superposition.
This square root of NOT is our example, not a gate specified in the thesis. -/
def mix : Op .bit .bit := fun i j =>
  if i = j then (1 + Complex.I) / 2 else (1 - Complex.I) / 2

theorem mix_dagger_epi : seq (dagger mix) mix = ident .bit := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  ext i j
  change (∑ k : Fin 2, mix i k * star (mix j k)) = if i = j then 1 else 0
  simp only [Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    norm_num [h01, h10, Space.Basis, Space.basisDecidableEq, mix, Complex.ext_iff]

end Op
end
end Foundation.Quantum
