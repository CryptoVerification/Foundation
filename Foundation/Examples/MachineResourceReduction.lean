import Foundation.Crypto.Semantics.Machine.ResourceReduction
import Foundation.Examples.ResourceSecurity

namespace CryptoLogic.MultiExamples

open Machine Machine.Examples
open scoped ENNReal

/-- A shared polynomial upper bound for the guarded compiler's execution. -/
def guardedResources : ResourceBounds :=
  ⟨fun m => 125 * (m + 1) * (twoStepResources.steps m + 1) ^ 2,
    twoStepResources.inputLength⟩

noncomputable def guardedResourceCertificate :
    (Reduction.id (ThreeGames.goal firstGame lastGame)).ResourceProgramReduction
      (ThreeGames.interface firstGame lastGame) (ThreeGames.interface firstGame lastGame)
      twoStepResources guardedResources :=
  Reduction.ResourceProgramReduction.ofSimulation
    (Reduction.MachineProgramTransformation.guarded
      (ThreeGames.interface firstGame lastGame)).toSimulation
    twoStepResources guardedResources
    (GuardedCompiler.rawTraceBudget_bound twoStepResources.steps)
    (fun _ h => h)

/-- The larger runtime bound still represents exactly the original attacker. -/
example :
    (ThreeGames.interface firstGame lastGame).Within guardedResources (fun _ => ())
      ((ThreeGames.interface firstGame lastGame).realizeFamily
        (fun _ => ()) randomOutputBit (fun _ => 2)) :=
  guardedResourceCertificate.mapWithin randomOutput_within

example (input : List Bool) :
    HaltsWithin (guardedResourceCertificate.compiler.run randomOutputBit) input
      (guardedResources.steps input.length) :=
  guardedResourceCertificate.halts randomOutputBit randomOutputBit_haltsWithin_any input

example : guardedResources.steps 0 = 1125 := by decide
example : guardedResources.steps 10 = 12375 := by decide

/-- Bridge a registered small-logic certificate to the uniform resource layer. -/
noncomputable def appendResourceCertificate :
    (appendCertificate firstGame lastGame).reduction.ResourceProgramReduction
      (ThreeGames.object firstGame lastGame).interface
      (ThreeGames.object firstGame lastGame).interface
      twoStepResources twoStepResources :=
  (appendCertificate firstGame lastGame).uniformResources
    twoStepResources twoStepResources (PolynomiallyBounded.const 2)
    (fun _ h m => le_of_eq (congrFun h m)) (fun _ h => h)

/-- The fixed target bounds for this order are intentionally supplied explicitly. -/
noncomputable def appendAfterGuarded :
    (appendCertificate firstGame lastGame).reduction.ResourceProgramReduction
      (ThreeGames.object firstGame lastGame).interface
      (ThreeGames.object firstGame lastGame).interface
      guardedResources guardedResources :=
  (appendCertificate firstGame lastGame).uniformResources
    guardedResources guardedResources
    (by
      exact ((PolynomiallyBounded.const 125).mul
        (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1))).mul
        (((PolynomiallyBounded.const 2).add (PolynomiallyBounded.const 1)).pow 2))
    (fun _ h m => le_of_eq (congrFun h m)) (fun _ h => h)

/-- Composition must execute the guarded compiler before appending halt. -/
example :
    (guardedResourceCertificate.comp appendAfterGuarded).compiler.run randomOutputBit =
      GuardedCompiler.rawCompile randomOutputBit ++ [.halt] := rfl

example (ε : Nat → ℝ≥0∞)
    (h : (ThreeGames.interface firstGame lastGame).ResourceSecure
      guardedResources (fun _ => ()) ε) :
    (ThreeGames.interface firstGame lastGame).ResourceSecure
      twoStepResources (fun _ => ()) ε :=
  (guardedResourceCertificate.comp appendAfterGuarded).resourceSecure (fun _ => ()) ε h

/-- Deliberately weaken the identity advantage bound to exercise an additive
error in the full resource-security theorem. This is a validation example. -/
noncomputable def relaxedReduction :
    Reduction (ThreeGames.goal firstGame lastGame) (ThreeGames.goal firstGame lastGame) where
  mapInstance := fun I => I
  reduce := fun _ A => A
  loss := AdvantageBound.affine (fun _ => 2) (fun _ => (1 : ℝ≥0∞) / 8)
  advantage_le := by
    intro n I A
    let x := (ThreeGames.goal firstGame lastGame).advantage n I A
    change x ≤ 2 * x + 1 / 8
    rw [two_mul]
    exact (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0∞) ≤ x)).trans
      (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0∞) ≤ 1 / 8))

noncomputable def relaxedResourceCertificate :
    relaxedReduction.ResourceProgramReduction
      (ThreeGames.interface firstGame lastGame) (ThreeGames.interface firstGame lastGame)
      twoStepResources guardedResources where
  compiler := guardedResourceCertificate.compiler
  halts := guardedResourceCertificate.halts
  realizes := guardedResourceCertificate.realizes
  inputLength := guardedResourceCertificate.inputLength

example (ε : Nat → ℝ≥0∞)
    (h : (ThreeGames.interface firstGame lastGame).ResourceSecure
      guardedResources (fun _ => ()) ε) :
    (ThreeGames.interface firstGame lastGame).ResourceSecure
      twoStepResources (fun _ => ()) (fun n => 2 * ε n + 1 / 8) :=
  relaxedResourceCertificate.resourceSecure_affine
    (fun _ => ()) (fun _ => 2) (fun _ => 1 / 8) ε rfl h

end CryptoLogic.MultiExamples
