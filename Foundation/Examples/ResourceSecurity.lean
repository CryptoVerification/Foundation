import Foundation.Crypto.Semantics.Machine.ResourceSecurity
import Foundation.Examples.MultiAssumption

namespace CryptoLogic.MultiExamples

open Machine Machine.Examples

def twoStepResources : ResourceBounds := ⟨fun _ => 2, fun n => n + 5⟩

/-- This class contains an actual two-step probabilistic program. -/
theorem randomOutput_within :
    (ThreeGames.interface firstGame lastGame).Within twoStepResources (fun _ => ())
      ((ThreeGames.interface firstGame lastGame).realizeFamily
        (fun _ => ()) randomOutputBit (fun _ => 2)) :=
  ⟨randomOutputBit, randomOutputBit_haltsWithin_any, sourceSize.length_le, rfl⟩

/-- Increasing fuel preserves the represented adversary, as well as halting. -/
example :
    (ThreeGames.interface firstGame lastGame).Within
      ⟨fun _ => 10, fun n => n + 8⟩ (fun _ => ())
      ((ThreeGames.interface firstGame lastGame).realizeFamily
        (fun _ => ()) randomOutputBit (fun _ => 2)) := by
  apply randomOutput_within.mono
  exact ⟨by intro m; change 2 ≤ 10; decide,
    by intro n; dsimp [twoStepResources]; omega⟩

example : twoStepResources.Polynomial :=
  ⟨PolynomiallyBounded.const 2,
    PolynomiallyBounded.id.add (PolynomiallyBounded.const 5)⟩

-- An input bound below the framed input length admits no adversary.
-- This checks that the definition actually enforces the protocol size condition.
set_option backward.isDefEq.respectTransparency false in
example (steps : Nat → Nat)
    (A : AdversaryFamily (ThreeGames.goal firstGame lastGame) (fun _ => ())) :
    ¬ (ThreeGames.interface firstGame lastGame).Within
      ⟨steps, fun n => n + 4⟩ (fun _ => ()) A := by
  rintro ⟨p, _, hSize, _⟩
  have h := hSize 0 false
  rw [MachineAdversaryInterface.machineInput_length] at h
  simp [ThreeGames.interface, FiniteBitEncoding.unit, FiniteBitEncoding.bool] at h

end CryptoLogic.MultiExamples
