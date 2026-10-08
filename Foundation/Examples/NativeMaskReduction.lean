import Foundation.Constructions.Symmetric.EncryptThenMAC.NativeMaskReductionBackend

/-! Concrete inhabitants of both registered reduction branches. Each uses a
single fixed finite observer program for every public parameter. No security
assumption about the challenge generator is needed for execution membership. -/
namespace Foundation.Examples.NativeMaskReduction
open Machine Foundation.Probability Foundation.Symmetric
open Foundation.Symmetric.EncryptThenMAC
open CryptoLogic.General
set_option backward.isDefEq.respectTransparency false
variable (G : Generator) (F : InstanceFamily G.prgGoal) (branch : Bool)
    (hWidth : PolynomiallyBounded G.outputLength)

noncomputable def firstWitness :=
  NativeMaskReductionBackend.witness G NativeObservers.first branch (fun _ => 3) F (fun _ => rfl)
    NativeObservers.first_halted (fun _ _ _ => Nat.le_refl _) hWidth (PolynomiallyBounded.const 3)

noncomputable def randomWitness :=
  NativeMaskReductionBackend.witness G NativeObservers.random branch (fun _ => 2) F (fun _ => rfl)
    NativeObservers.random_halted (fun _ _ _ => Nat.le_refl _) hWidth (PolynomiallyBounded.const 2)

theorem firstWitness_code : (firstWitness G F branch hWidth).code = NativeObservers.firstCode := rfl

theorem randomWitness_code : (randomWitness G F branch hWidth).code = NativeObservers.randomCode := rfl

theorem firstWitness_queries : (firstWitness G F branch hWidth).resources.2 = (fun _ => 1) := rfl

theorem firstWitness_horizon (n : Nat) :
    (firstWitness G F branch hWidth).resources.1.horizon n = 52 * G.outputLength n + 45 := by
  change 52 * G.outputLength n + 42 + 3 = _
  omega

theorem both_branches_same_code :
    (firstWitness G F false hWidth).code = (firstWitness G F true hWidth).code := rfl

end Foundation.Examples.NativeMaskReduction
