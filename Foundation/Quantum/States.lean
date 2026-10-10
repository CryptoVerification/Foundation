import Foundation.Quantum.Finite
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Finite density operators and Kraus operations. This probabilistic layer is
additional quantum-information mathematics, not Heunen's dagger-epi measurement. -/
namespace Foundation.Quantum
noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false

abbrev Operator (a : Space) := Op a a

structure Density (a : Space) where
  matrix : Operator a
  positive : matrix.PosSemidef
  normalized : matrix.trace = 1

/-- A finite Kraus family; no preservation condition is silently assumed. -/
structure Kraus (a b : Space) where
  index : Type
  finite : Fintype index
  operator : index → Op a b

attribute [instance] Kraus.finite

namespace Kraus
variable {a b c : Space}

def apply (K : Kraus a b) (ρ : Operator a) : Operator b :=
  ∑ k, K.operator k * ρ * (K.operator k).conjTranspose

/-- The Kraus operation is genuinely complex-linear on operators. -/
def linear (K : Kraus a b) : Operator a →ₗ[ℂ] Operator b where
  toFun := K.apply
  map_add' ρ σ := by
    simp [apply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' z ρ := by
    simp [apply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

def effect (K : Kraus a b) : Operator a :=
  ∑ k, (K.operator k).conjTranspose * K.operator k

theorem positive (K : Kraus a b) {ρ : Operator a} (hρ : ρ.PosSemidef) :
    (K.apply ρ).PosSemidef :=
  Matrix.posSemidef_sum _ (fun _ _ => hρ.mul_mul_conjTranspose_same _)

theorem trace_apply (K : Kraus a b) (ρ : Operator a) :
    (K.apply ρ).trace = (K.effect * ρ).trace := by
  simp only [apply, effect, Matrix.trace_sum, Matrix.sum_mul]
  congr 1
  funext k
  rw [Matrix.trace_mul_cycle]

/-- Acting on one subsystem while retaining an arbitrary finite auxiliary system. -/
def amplify (K : Kraus a b) (e : Space) : Kraus (.tensor a e) (.tensor b e) :=
  ⟨K.index, K.finite, fun k => Op.tensor (K.operator k) (Op.ident e)⟩

/-- Entry formula identifies the amplification with acting on the system and
leaving each auxiliary matrix coordinate untouched. -/
theorem amplify_apply_entry (K : Kraus a b) (e : Space)
    (ρ : Operator (.tensor a e)) (i j : b.Basis) (u v : e.Basis) :
    (K.amplify e).apply ρ (i, u) (j, v) =
      ∑ k, ∑ s : a.Basis, ∑ t : a.Basis,
        K.operator k i s * ρ (s, u) (t, v) * star (K.operator k j t) := by
  simp [apply, amplify, Op.tensor, Op.ident, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Space.Basis, apply_ite,
    ite_mul, Finset.sum_mul, -Finset.sum_boole]
  congr 1
  funext k
  exact Finset.sum_comm

/-- Complete positivity is proved at every auxiliary dimension, including entangled inputs. -/
theorem completely_positive (K : Kraus a b) (e : Space)
    {ρ : Operator (.tensor a e)} (hρ : ρ.PosSemidef) :
    ((K.amplify e).apply ρ).PosSemidef := (K.amplify e).positive hρ

def single (M : Op a b) : Kraus a b := ⟨Unit, inferInstance, fun _ => M⟩

@[simp] theorem single_apply (M : Op a b) (ρ : Operator a) :
    (single M).apply ρ = M * ρ * M.conjTranspose := by simp [apply, single]

@[simp] theorem single_effect (M : Op a b) :
    (single M).effect = M.conjTranspose * M := by simp [effect, single]

theorem amplify_effect (K : Kraus a b) (e : Space) :
    (K.amplify e).effect = Op.tensor K.effect (Op.ident e) := by
  have h (k : K.index) :
      (Op.tensor (K.operator k) (Op.ident e)).conjTranspose *
        Op.tensor (K.operator k) (Op.ident e) =
      Op.tensor ((K.operator k).conjTranspose * K.operator k) (Op.ident e) := by
    have hc := Matrix.conjTranspose_kronecker (K.operator k) (1 : Op e e)
    change (Matrix.kronecker (K.operator k) (1 : Op e e)).conjTranspose *
      Matrix.kronecker (K.operator k) (1 : Op e e) = _
    unfold Matrix.kronecker
    rw [hc]
    have hm := (Matrix.mul_kronecker_mul (K.operator k).conjTranspose (K.operator k)
      (1 : Op e e).conjTranspose (1 : Op e e)).symm
    exact hm.trans (by simp [Op.tensor, Op.ident, Matrix.kronecker])
  change (∑ k, (Op.tensor (K.operator k) (Op.ident e)).conjTranspose *
    Op.tensor (K.operator k) (Op.ident e)) = Op.tensor K.effect (Op.ident e)
  simp_rw [h]
  ext i j
  simp [effect, Op.tensor, Matrix.kronecker, Matrix.kroneckerMap, Matrix.sum_apply, Finset.sum_mul]

/-- Sequential composition sums over both physical outcome indices. -/
def seq (K : Kraus a b) (L : Kraus b c) : Kraus a c :=
  ⟨K.index × L.index, inferInstance, fun p => L.operator p.2 * K.operator p.1⟩

theorem seq_apply (K : Kraus a b) (L : Kraus b c) (ρ : Operator a) :
    (K.seq L).apply ρ = L.apply (K.apply ρ) := by
  simp only [apply, seq, Matrix.conjTranspose_mul, Fintype.sum_prod_type,
    Matrix.mul_sum, Matrix.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  funext l
  congr 1
  funext k
  simp only [Matrix.mul_assoc]

end Kraus

/-- A channel is a Kraus operation with its normalization verified. -/
structure Channel (a b : Space) extends Kraus a b where
  complete : toKraus.effect = 1

namespace Channel
variable {a b : Space}

def run (C : Channel a b) (ρ : Density a) : Density b where
  matrix := C.toKraus.apply ρ.matrix
  positive := C.toKraus.positive ρ.positive
  normalized := by rw [C.toKraus.trace_apply, C.complete, Matrix.one_mul, ρ.normalized]

/-- Only isometries lift to one-Kraus deterministic channels. -/
def ofIsometry (M : Op a b) (h : M.conjTranspose * M = 1) : Channel a b :=
  ⟨Kraus.single M, by simpa using h⟩

def identity (a : Space) : Channel a a := ofIsometry 1 (by simp)

def amplify (C : Channel a b) (e : Space) : Channel (.tensor a e) (.tensor b e) where
  toKraus := C.toKraus.amplify e
  complete := by
    rw [Kraus.amplify_effect, C.complete]
    exact Matrix.one_kronecker_one

def seq {c : Space} (C : Channel a b) (D : Channel b c) : Channel a c where
  toKraus := C.toKraus.seq D.toKraus
  complete := by
    change (∑ p : C.index × D.index,
      (D.operator p.2 * C.operator p.1).conjTranspose *
        (D.operator p.2 * C.operator p.1)) = 1
    simp only [Fintype.sum_prod_type, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp_rw [← Matrix.mul_assoc (D.operator _).conjTranspose]
    simp_rw [← Matrix.mul_sum, ← Matrix.sum_mul]
    change (∑ k, (C.operator k).conjTranspose * (D.toKraus.effect * C.operator k)) = 1
    rw [D.complete]
    simpa [Kraus.effect] using C.complete

end Channel

/-- Every chosen basis vector gives a normalized, positive state. -/
def basisDensity (a : Space) (i : a.Basis) : Density a where
  matrix := Matrix.diagonal (fun j => if j = i then 1 else 0)
  positive := Matrix.PosSemidef.diagonal (by intro j; dsimp; split_ifs <;> simp)
  normalized := by simp [Matrix.trace, Matrix.diag]

end
end Foundation.Quantum
