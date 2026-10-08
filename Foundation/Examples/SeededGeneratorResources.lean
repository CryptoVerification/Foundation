import Foundation.Examples.TypedSeedPrecondition
import Foundation.Constructions.Symmetric.EncryptThenMAC.SeededGeneratorResources
import Foundation.Crypto.Semantics.Machine.NativeObservers

/-! Whole-prefix encoded storage for the guarded arbitrary-width native seed
component, real masking and either finite observer. The component need not
terminate on malformed layouts. Its identity output is not a stretching PRG. -/
namespace Foundation.Examples.SeededGeneratorResources
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC
open ReusableBlockPad.NativeObserver (RuntimeState boundary publicMachine)
open TypedSeedPrecondition (generator expander)
set_option backward.isDefEq.respectTransparency false

theorem generator_space_polynomial : PolynomiallyBounded expander.generatorBitBound :=
  expander.generatorBitBound_polynomial PolynomiallyBounded.id (PolynomiallyBounded.const 2)

theorem encryption_space_polynomial (observer : Machine.Program) {observerCap : Nat → Nat}
    (hObserver : PolynomiallyBounded observerCap) :
    PolynomiallyBounded (expander.encryptionBitBound observer observerCap) :=
  expander.encryptionBitBound_polynomial observer observerCap PolynomiallyBounded.id
    (PolynomiallyBounded.const 2) PolynomiallyBounded.id hObserver

theorem first_space_polynomial :
    PolynomiallyBounded (expander.encryptionBitBound NativeObservers.firstCode (fun _ => 3)) :=
  encryption_space_polynomial NativeObservers.firstCode (PolynomiallyBounded.const 3)

theorem random_space_polynomial :
    PolynomiallyBounded (expander.encryptionBitBound NativeObservers.randomCode (fun _ => 2)) :=
  encryption_space_polynomial NativeObservers.randomCode (PolynomiallyBounded.const 2)

/-- Fixed generator and observer codes; all supported intermediate states
are counted, including private key and original caller during observation. -/
theorem peak (width : Nat) (message : Bits width) (observer : Machine.Program)
    (observerCap : Nat → Nat) (elapsed : Nat)
    (hElapsed : elapsed ≤ 55 * width + 45 + observerCap width)
    (target : NativeContinuation.Control (RuntimeState Unit))
    (hTarget : target ∈ (TimedExecution.eval
      (NativeContinuation.step
        (ProjectedGeneratedBlockMask.step (expander.projected.native width)
          ReusableBlockPadEncodedBackend.unitOracle () [] message)
        boundary publicMachine observer) elapsed
      (.producing (ProjectedGeneratedBlockMask.Resources.initial (expander.projected.native width) ()))).support) :
    ((ProjectedGeneratedBlockMask.NativeObserver.Resources.completeEncoding () [] message FiniteBitEncoding.unit).encode
      (OneTimePad.keygen.followedBy TypedSeedPrecondition.code, PrivateKeyCopy.code,
        FlaggedBlockXor.code, ReusableBlockPad.code, (observer, target))).length ≤
      expander.encryptionBitBound observer observerCap width := by
  apply expander.encryption_peak width message observer observerCap elapsed _ target hTarget
  change  elapsed ≤ 5 * width + 2 + 3 + 50 * width + 40 + observerCap width
  omega

end Foundation.Examples.SeededGeneratorResources
