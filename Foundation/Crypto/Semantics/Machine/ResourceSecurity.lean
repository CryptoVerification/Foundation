import Foundation.Crypto.Semantics.Machine.PPT
import Foundation.Crypto.Semantics.Security.Asymptotic

/-! Concrete resource-restricted security for the existing one-request machine
adapter. Steps are measured in total input bit length; input length is measured
in the security parameter. Neither oracle-query counts nor the external
adapter's running time are included. -/

namespace Machine

open scoped ENNReal

universe u v w

/-- Concrete bounds need not be polynomial. One response execution must halt
on every input and every random branch within `steps input.length`. -/
structure ResourceBounds where
  steps : Nat → Nat
  inputLength : Nat → Nat

namespace ResourceBounds

def LE (R S : ResourceBounds) : Prop :=
  (∀ m, R.steps m ≤ S.steps m) ∧ (∀ n, R.inputLength n ≤ S.inputLength n)

def Polynomial (R : ResourceBounds) : Prop :=
  PolynomiallyBounded R.steps ∧ PolynomiallyBounded R.inputLength

end ResourceBounds

namespace MachineAdversaryInterface

/-- A single finite program realizes the entire family. The input-size
condition is universal over requests, just as in the existing PPT class. -/
def Within {P : CryptoGoal.{u}} (J : MachineAdversaryInterface.{u, v, w} P)
    (R : ResourceBounds) (F : InstanceFamily P) (A : AdversaryFamily P F) : Prop :=
  ∃ p : Program,
    (∀ input : List Bool, HaltsWithin p input (R.steps input.length)) ∧
    (∀ n (request : J.Request n (F n)),
      (J.machineInput n (F n) request).length ≤ R.inputLength n) ∧
    J.Realizes F p R.steps A

def resourceClass {P : CryptoGoal.{u}} (J : MachineAdversaryInterface.{u, v, w} P)
    (R : ResourceBounds) : AdversaryClass P where
  admissible := J.Within R

/-- One common advantage bound for every family inside the resource bounds.
This is a uniform bound; it is stronger than individual negligibility. -/
def ResourceSecure {P : CryptoGoal.{u}} (J : MachineAdversaryInterface.{u, v, w} P)
    (R : ResourceBounds) (F : InstanceFamily P) (ε : Nat → ℝ≥0∞) : Prop :=
  BoundedByOnWithin P (J.resourceClass R) F ε

theorem Within.mono {P : CryptoGoal.{u}} {J : MachineAdversaryInterface.{u, v, w} P}
    {R S : ResourceBounds} {F : InstanceFamily P} {A : AdversaryFamily P F}
    (h : J.Within R F A) (hRS : R.LE S) : J.Within S F A := by
  obtain ⟨p, hHalts, hSize, hRealizes⟩ := h
  have hHalts' : ∀ input : List Bool, HaltsWithin p input (S.steps input.length) :=
    fun input => (hHalts input).mono (hRS.1 _)
  refine ⟨p, hHalts', fun n request => (hSize n request).trans (hRS.2 n), ?_⟩
  exact (J.realizeFamily_budget_eq_of_halts F p R.steps S.steps hHalts hHalts').symm.trans
    hRealizes

/-- Fewer resources and a looser advantage bound preserve security. -/
theorem ResourceSecure.mono {P : CryptoGoal.{u}}
    {J : MachineAdversaryInterface.{u, v, w} P} {R S : ResourceBounds}
    {F : InstanceFamily P} {ε δ : Nat → ℝ≥0∞}
    (h : J.ResourceSecure S F ε) (hRS : R.LE S) (hεδ : ∀ n, ε n ≤ δ n) :
    J.ResourceSecure R F δ := by
  intro A hA n
  exact (h A (hA.mono hRS) n).trans (hεδ n)

theorem Within.ppt {P : CryptoGoal.{u}} {J : MachineAdversaryInterface.{u, v, w} P}
    {R : ResourceBounds} {F : InstanceFamily P} {A : AdversaryFamily P F}
    (h : J.Within R F A) (hR : R.Polynomial) : J.pptClass.admissible F A := by
  obtain ⟨p, hHalts, hSize, hRealizes⟩ := h
  exact ⟨p, R.steps, ⟨R.inputLength, hSize⟩, hR.1, hHalts, hR.2, hRealizes⟩

/-- The resource classes cover exactly the existing PPT class when both
bounds are polynomial. The bounds may depend on the individual adversary. -/
theorem ppt_iff_exists_resources {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P)
    (F : InstanceFamily P) (A : AdversaryFamily P F) :
    J.pptClass.admissible F A ↔ ∃ R : ResourceBounds, R.Polynomial ∧ J.Within R F A := by
  constructor
  · rintro ⟨p, q, size, hq, hHalts, hSize, hRealizes⟩
    exact ⟨⟨q, size.limit⟩, ⟨hq, hSize⟩, p, hHalts, size.length_le, hRealizes⟩
  · rintro ⟨R, hR, hA⟩
    exact hA.ppt hR

/-- A common negligible bound implies asymptotic security for this resource
class only. It does not automatically cover all polynomial resource bounds. -/
theorem ResourceSecure.asymptotic {P : CryptoGoal.{u}}
    {J : MachineAdversaryInterface.{u, v, w} P} {R : ResourceBounds}
    {F : InstanceFamily P} {ε : Nat → ℝ≥0∞}
    (h : J.ResourceSecure R F ε) (hε : Negligible ε) :
    SecureOnWithin P (J.resourceClass R) F :=
  SecureOnWithin.of_boundedBy h hε

/-- Covering all polynomial resource classes is equivalent to PPT security.
No common negligible bound across adversaries or resource bounds is needed. -/
theorem securePPT_iff_all_resources {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, v, w} P) (F : InstanceFamily P) :
    SecureOnWithin P J.pptClass F ↔
      ∀ R : ResourceBounds, R.Polynomial → SecureOnWithin P (J.resourceClass R) F := by
  constructor
  · intro h R hR A hA
    exact h A (hA.ppt hR)
  · intro h A hA
    obtain ⟨R, hR, hWithin⟩ := (J.ppt_iff_exists_resources F A).mp hA
    exact h R hR A hWithin

end MachineAdversaryInterface
end Machine
