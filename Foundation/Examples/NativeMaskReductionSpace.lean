import Foundation.Constructions.Symmetric.EncryptThenMAC.NativeMaskReductionSpaceBackend

/-! Fixed deterministic and randomized observer examples with simultaneous
time, one-query and faithful whole-prefix encoded-space certificates. -/
namespace Foundation.Examples.NativeMaskReductionSpace
open Machine Foundation.Probability Foundation.Symmetric
open Foundation.Symmetric.EncryptThenMAC
open CryptoLogic.General
set_option backward.isDefEq.respectTransparency false
variable (G : Generator) (F : InstanceFamily G.prgGoal) (branch : Bool)
    (hWidth : PolynomiallyBounded G.outputLength)

noncomputable def firstWitness :=
  NativeMaskReductionSpaceBackend.witness G NativeObservers.first branch (fun _ => 3) F
    hWidth (PolynomiallyBounded.const 3) (fun _ => rfl)
    NativeObservers.first_halted (fun _ _ _ => Nat.le_refl _)

noncomputable def randomWitness :=
  NativeMaskReductionSpaceBackend.witness G NativeObservers.random branch (fun _ => 2) F
    hWidth (PolynomiallyBounded.const 2) (fun _ => rfl)
    NativeObservers.random_halted (fun _ _ _ => Nat.le_refl _)

theorem firstWitness_code : (firstWitness G F branch hWidth).code = NativeObservers.firstCode := rfl

theorem randomWitness_code : (randomWitness G F branch hWidth).code = NativeObservers.randomCode := rfl

theorem firstWitness_queries : (firstWitness G F branch hWidth).resources.1.2 = (fun _ => 1) := rfl

theorem firstWitness_horizon (n : Nat) :
    (firstWitness G F branch hWidth).resources.1.1.horizon n = 52 * G.outputLength n + 45 := by
  change 52 * G.outputLength n + 42 + 3 = _
  omega

theorem firstWitness_space (n : Nat) :
    (firstWitness G F branch hWidth).resources.2 n =
      NativeMaskChallenge.WholeResources.bitBound NativeObservers.firstCode (G.outputLength n)
        (52 * G.outputLength n + 45) := by
  change NativeMaskChallenge.WholeResources.bitBound _ _ (52 * G.outputLength n + 42 + 3) = _
  exact congrArg (NativeMaskChallenge.WholeResources.bitBound NativeObservers.firstCode
    (G.outputLength n)) (by omega)

theorem firstWitness_space_polynomial :
    PolynomiallyBounded (firstWitness G F branch hWidth).resources.2 :=
  NativeMaskReductionSpaceBackend.bitCap_polynomial G NativeObservers.firstCode (fun _ => 3)
    hWidth (PolynomiallyBounded.const 3)

theorem both_branches_same_code :
    (firstWitness G F false hWidth).code = (firstWitness G F true hWidth).code :=
  (firstWitness_code G F false hWidth).trans (firstWitness_code G F true hWidth).symm

end Foundation.Examples.NativeMaskReductionSpace
