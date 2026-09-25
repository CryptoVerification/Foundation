import Foundation.Core.Reduction

open scoped ENNReal

namespace Foundation.Examples

def A : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun _ _ => Unit
  advantage := fun _ _ _ => 0

def B : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun _ _ => Unit
  advantage := fun _ _ _ => 0

def C : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun _ _ => Unit
  advantage := fun _ _ _ => 0

def R₁ : Reduction A B where
  mapInstance := fun _ => ()
  reduce := fun _ _ => ()
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
  reduce := fun _ _ => ()
  loss := {
    eval := fun _ x => x + 2
    monotone := by
      intro _ _ _ h
      exact add_le_add_left h 2
  }
  advantage_le := by
    intro _ _ _
    exact zero_le

def R₃ : Reduction A C := Reduction.comp R₁ R₂

theorem composed_loss (n : Nat) (x : ℝ≥0∞) :
    R₃.loss.eval n x = (x + 2) + 1 := by
  rfl

end Foundation.Examples
