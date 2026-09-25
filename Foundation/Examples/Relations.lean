import Foundation.Core.SecurityBound
import Foundation.Relation.Equivalence

open scoped ENNReal

namespace Foundation.Examples.Relations

def A : CryptoGoal where
  Instance := fun n => Fin (n + 1)
  Adversary := fun _ _ => Bool
  advantage := fun _ _ _ => 0

def B : CryptoGoal where
  Instance := fun _ => Bool
  Adversary := fun _ _ => Fin 3
  advantage := fun _ _ _ => 0

def C : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun _ _ => Nat
  advantage := fun _ _ _ => 0

def R₁ : Reduction A B where
  mapInstance := fun _ => false
  reduce := fun _ _ => (0 : Fin 3)
  loss := {
    eval := fun _ x => x + 1
    monotone := by
      intro _ _ _ h
      exact add_le_add_left h 1
  }
  advantage_le := by
    intro _ _ _
    exact zero_le

def R₂ : Reduction B C where
  mapInstance := fun _ => ()
  reduce := fun _ _ => (0 : Nat)
  loss := {
    eval := fun _ x => x + 2
    monotone := by
      intro _ _ _ h
      exact add_le_add_left h 2
  }
  advantage_le := by
    intro _ _ _
    exact zero_le

def R₃ : Reduction A C := R₁.comp R₂

theorem reducesAB : ReducesTo A B := ⟨R₁⟩

theorem reducesBC : ReducesTo B C := ⟨R₂⟩

theorem reducesAC : ReducesTo A C :=
  ReducesTo.trans reducesAB reducesBC

theorem composedLoss (n : Nat) (x : ℝ≥0∞) :
    R₃.loss.eval n x = (x + 2) + 1 := by
  rfl

theorem transportedBound (ε : Nat → ℝ≥0∞) (hC : BoundedBy C ε) :
    BoundedBy A (fun n => R₁.loss.eval n (R₂.loss.eval n (ε n))) :=
  (R₁.comp R₂).boundedBy hC

theorem transportedBoundConcrete (ε : Nat → ℝ≥0∞) (hC : BoundedBy C ε) :
    BoundedBy A (fun n => (ε n + 2) + 1) :=
  R₃.boundedBy hC

def FA : InstanceFamily A := fun n => ⟨0, Nat.zero_lt_succ n⟩

def FB : InstanceFamily B := R₁.mapFamily FA

def FC : InstanceFamily C := R₂.mapFamily FB

theorem mappedFamilyComp : R₃.mapFamily FA = FC := by
  exact Reduction.mapFamily_comp R₁ R₂ FA

theorem transportedFamilySequential (ε : Nat → ℝ≥0∞)
    (hC : BoundedByOn C FC ε) :
    BoundedByOn A FA (fun n => R₁.loss.eval n (R₂.loss.eval n (ε n))) :=
  R₁.boundedByOn FA (R₂.boundedByOn FB hC)

theorem transportedFamilyComposed (ε : Nat → ℝ≥0∞)
    (hC : BoundedByOn C FC ε) :
    BoundedByOn A FA (fun n => R₁.loss.eval n (R₂.loss.eval n (ε n))) := by
  have hMapped : BoundedByOn C (R₃.mapFamily FA) ε := by
    rw [mappedFamilyComp]
    exact hC
  exact R₃.boundedByOn FA hMapped

theorem transportedFamilyConcrete (ε : Nat → ℝ≥0∞)
    (hC : BoundedByOn C FC ε) :
    BoundedByOn A FA (fun n => (ε n + 2) + 1) :=
  transportedFamilyComposed ε hC

end Foundation.Examples.Relations
