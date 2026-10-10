import Foundation.Quantum.QKD.HashLogic
import Foundation.Quantum.QKD.BB84BlockExamples

/-! Concrete optional raw inputs and a mixed finite derivation. An absent
position and a zero bit remain distinct inputs. The BB84 state example uses
the already verified joint CNOT attack, not independent single-signal attacks. -/
namespace Foundation.Quantum.QKD.HashExamples
noncomputable section
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false

def absent : Finalization.RawKey 1 := fun _ => none
def zeroBit : Finalization.RawKey 1 := fun _ => some 0
def oneBit : Finalization.RawKey 1 := fun _ => some 1

theorem absent_ne_zero : absent ≠ zeroBit := by
  intro h
  have hh := congrFun h 0
  simp [absent,zeroBit] at hh

theorem zero_ne_one_bit : zeroBit ≠ oneBit := by
  intro h
  have hh := congrFun h 0
  norm_num [zeroBit,oneBit] at hh

theorem absent_zero_collision :
    (Foundation.Probability.eventProb (Foundation.Probability.uniform (Hashing.RawSeed 1 2))
      (fun M => Hashing.rawHash M absent = Hashing.rawHash M zeroBit)).toReal = 1/4 := by
  have h := Hashing.raw_collision (length := 2) absent zeroBit absent_ne_zero
  norm_num at h ⊢
  exact h

def experiments : Fin 2 → HashLogic.Experiment 1 := fun i =>
  if i = 0 then .pair absent zeroBit else .pair zeroBit oneBit

def mixedExperiment : HashLogic.Experiment 1 :=
  .mixture 2 (Foundation.Probability.uniform (Fin 2)) experiments

/-- A finite proof mixes two verified collision bounds and normalizes the resulting error. -/
def mixedProof : Derivation (HashLogic.presentation 1 2) (Logic.Context.empty (HashLogic.presentation 1 2))
    (mixedExperiment,1/4) := by
  apply Derivation.apply (T := HashLogic.presentation 1 2)
    (.weaken mixedExperiment (∑ i : Fin 2, ((Foundation.Probability.uniform (Fin 2)) i).toReal * (1/(2:ℝ)^2))
      (1/4) (by rw [← Finset.sum_mul, Density.probability_weights]; norm_num))
  intro _
  apply Derivation.apply (T := HashLogic.presentation 1 2)
    (.mixture 2 (Foundation.Probability.uniform (Fin 2)) experiments (fun _ => 1/(2:ℝ)^2))
  intro i
  change Fin 2 at i
  by_cases hi : i = 0
  · subst i
    exact .apply (T := HashLogic.presentation 1 2) (.linear absent zeroBit absent_ne_zero) (fun i => Fin.elim0 i)
  · have h1 : i = 1 := by omega
    subst i
    exact .apply (T := HashLogic.presentation 1 2) (.linear zeroBit oneBit zero_ne_one_bit) (fun i => Fin.elim0 i)

theorem mixed_interpreted : HashLogic.probability 2 mixedExperiment ≤ 1/4 :=
  HashLogic.sound 1 2 mixedProof (fun i => Fin.elim0 i)

/-- This concrete matrix distinguishes an absent raw position from a zero bit. -/
def presenceSeed : Hashing.RawSeed 1 2 := fun _ p => if p.2 = 0 then 1 else 0

theorem presence_separates : Hashing.rawHash presenceSeed absent ≠ Hashing.rawHash presenceSeed zeroBit := by
  intro h
  have hh := congrFun h 0
  norm_num [Hashing.rawHash, Hashing.linearHash, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Hashing.encodeRaw, absent, zeroBit, presenceSeed, Fin.sum_univ_succ] at hh

/-- The genuinely joint two-signal attack is processed by the concrete
 uniformly seeded family while Eve's retained system remains in the density. -/
def cnotHashed : Density (.tensor
    (IdealKey.register (Finalization.Transcript 2 (Hashing.RawSeed 2 1)) 1) .unit) :=
  Hashing.linearState (length := 1) BlockExamples.cnotAttack 1 1 0

theorem cnotHashed_ideal_public :
    ((IdealKey.publicChannel .unit).run (IdealKey.idealize cnotHashed)).matrix =
      ((IdealKey.publicChannel .unit).run cnotHashed).matrix := IdealKey.public_idealize _

end
end Foundation.Quantum.QKD.HashExamples
