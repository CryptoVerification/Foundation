import Foundation.Asymptotics.Negligible
import Foundation.Resource.Adversary

open scoped ENNReal

universe u

/-- On instance family `F`, every adversary family admitted by `C` has a
negligible advantage profile. Each adversary family has its own asymptotic
bound; no common negligible bound is required. -/
def SecureOnWithin (P : CryptoGoal.{u}) (C : AdversaryClass P)
    (F : InstanceFamily P) : Prop :=
  ∀ (A : AdversaryFamily P F), C.admissible F A →
    Negligible (advantageProfile P F A)

namespace SecureOnWithin

/-- A common negligible concrete bound is sufficient for security. -/
theorem of_boundedBy {P : CryptoGoal.{u}} {C : AdversaryClass P}
    {F : InstanceFamily P} {ε : Nat → ℝ≥0∞}
    (hBound : BoundedByOnWithin P C F ε) (hNeg : Negligible ε) :
    SecureOnWithin P C F := by
  intro A hA
  apply Negligible.mono _ hNeg
  intro n
  exact hBound A hA n

/-- The existing unrestricted concrete bound yields security for any class
when its bound is negligible. -/
theorem of_boundedByOn {P : CryptoGoal.{u}}
    {F : InstanceFamily P} {ε : Nat → ℝ≥0∞}
    (hBound : BoundedByOn P F ε) (hNeg : Negligible ε)
    (C : AdversaryClass P) : SecureOnWithin P C F :=
  of_boundedBy (hBound.within C) hNeg

/-- Security persists when the new class admits only families admitted by
the original class. -/
theorem monoClass {P : CryptoGoal.{u}} {C D : AdversaryClass P}
    {F : InstanceFamily P}
    (hDC : ∀ (G : InstanceFamily P) (A : AdversaryFamily P G),
      D.admissible G A → C.admissible G A)
    (hSec : SecureOnWithin P C F) : SecureOnWithin P D F := by
  intro A hA
  exact hSec A (hDC F A hA)

end SecureOnWithin
