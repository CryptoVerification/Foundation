import Foundation.Crypto.Semantics.Machine.NativeEncodedResources
import Foundation.Crypto.Semantics.Oracle.PrivateControllerAddresses
import Foundation.Crypto.Semantics.Oracle.ControllerExtentExecution

/-! Whole private-controller bit bounds. The representation retains the
three finite programs as well as every runtime state. Address growth and
retained-data growth are derived from the actual physical transitions. -/
namespace CryptoOracle.Interactive.PrivateControllerEncoding
open Machine Foundation.Probability
universe u
variable {State : Type u}

def programEncoding : FiniteBitEncoding Machine.Program :=
  Machine.Program.bitEncoding

def completeEncoding (E : FiniteBitEncoding State) :=
  programEncoding.prod (programEncoding.prod (EncodedStorage.codeEncoding.prod (initializationRuntime E)))

def codeBits (generator native : Machine.Program) (code : Code) : Nat :=
  2 * (Program.encode generator).length + 2 * (Program.encode native).length +
    2 * (EncodedStorage.codeEncoding.encode code).length + 3

def encodedBound (generator native : Machine.Program) (code : Code)
    (initialAddress initialExtent horizon stateIncrement responseCap : Nat) : Nat :=
  let address := initialAddress + horizon * (generator.addressCap + native.addressCap + EncodedStorage.addressCap code + 1)
  let extent := initialExtent + horizon * (stateIncrement + responseCap + 2)
  codeBits generator native code + 32 * address +
    144 * (4 * extent ^ 2 + 11 * extent + 2) + 16 * extent + 256

theorem complete_length (E : FiniteBitEncoding State) (generator native : Machine.Program) (code : Code)
    (caller : Configuration State) (c : OneUseInitialization.Control State) :
    ((completeEncoding E).encode (generator, native, code, runtime caller c)).length =
      codeBits generator native code + ((initializationRuntime E).encode (runtime caller c)).length := by
  simp only [completeEncoding, FiniteBitEncoding.prod_encode_length, programEncoding, Program.bitEncoding, codeBits]
  omega

theorem encoded_peak (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (generator native : Machine.Program) (code : Code) (oracle : BitOracle State) (caller : Configuration State)
    (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start target : OneUseInitialization.Control State)
    (hTarget : target ∈ (TimedExecution.eval
      (OneUseInitialization.step generator native code oracle caller) elapsed start).support) :
    ((completeEncoding E).encode (generator, native, code, runtime caller target)).length ≤
      encodedBound generator native code (initializationMaxPc caller start)
        (ControllerExtent.initializationExtent stateSize caller start) horizon stateIncrement responseCap := by
  have ha := TimedExecution.ResourceGrowth.prefix_bound
    (OneUseInitialization.step generator native code oracle caller) (initializationMaxPc caller)
    (generator.addressCap + native.addressCap + EncodedStorage.addressCap code + 1)
    (initialization_max_pc_step generator native code oracle caller) horizon elapsed hElapsed start target hTarget
  have he := TimedExecution.ResourceGrowth.prefix_bound
    (OneUseInitialization.step generator native code oracle caller) (ControllerExtent.initializationExtent stateSize caller)
    (stateIncrement + responseCap + 2)
    (ControllerExtent.initialization_step stateSize generator native code oracle caller stateIncrement responseCap hOracle)
    horizon elapsed hElapsed start target hTarget
  have hs := initializationPc_le_twice caller target
  have hl := initialization_extent_length_le E stateSize hState caller target
  have hq := Nat.pow_le_pow_left he 2
  rw [complete_length]
  dsimp only [encodedBound]
  omega

theorem encodedBound_polynomial (generator native : Machine.Program) (code : Code)
    {initialAddress initialExtent horizon stateIncrement responseCap : Nat → Nat}
    (hAddress : PolynomiallyBounded initialAddress) (hExtent : PolynomiallyBounded initialExtent)
    (hTime : PolynomiallyBounded horizon) (hIncrement : PolynomiallyBounded stateIncrement)
    (hResponse : PolynomiallyBounded responseCap) :
    PolynomiallyBounded (fun n => encodedBound generator native code (initialAddress n) (initialExtent n)
      (horizon n) (stateIncrement n) (responseCap n)) := by
  have ha := hAddress.add (hTime.mul (PolynomiallyBounded.const
    (generator.addressCap + native.addressCap + EncodedStorage.addressCap code + 1)))
  have he := hExtent.add (hTime.mul ((hIncrement.add hResponse).add (PolynomiallyBounded.const 2)))
  have hq := (((PolynomiallyBounded.const 4).mul (he.mul he)).add
    ((PolynomiallyBounded.const 11).mul he)).add (PolynomiallyBounded.const 2)
  have hb := (((((PolynomiallyBounded.const (codeBits generator native code)).add
    ((PolynomiallyBounded.const 32).mul ha)).add ((PolynomiallyBounded.const 144).mul hq)).add
      ((PolynomiallyBounded.const 16).mul he)).add (PolynomiallyBounded.const 256))
  simpa only [encodedBound, pow_two] using hb

theorem encodedBound_mono_initial (generator native : Machine.Program) (code : Code)
    {firstAddress secondAddress firstExtent secondExtent : Nat}
    (hAddress : firstAddress ≤ secondAddress) (hExtent : firstExtent ≤ secondExtent)
    (horizon stateIncrement responseCap : Nat) :
    encodedBound generator native code firstAddress firstExtent horizon stateIncrement responseCap ≤
      encodedBound generator native code secondAddress secondExtent horizon stateIncrement responseCap := by
  have he := Nat.add_le_add_right hExtent (horizon * (stateIncrement + responseCap + 2))
  have hq := Nat.pow_le_pow_left he 2
  dsimp only [encodedBound]
  omega

end CryptoOracle.Interactive.PrivateControllerEncoding
