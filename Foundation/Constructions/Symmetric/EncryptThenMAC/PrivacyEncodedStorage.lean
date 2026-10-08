import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyAddresses
import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyStorageExecution
import Foundation.Crypto.Semantics.Oracle.PrivateEncodedStorage

/-! Whole finite-code and state bit bounds for the actual privacy reduction.
The shared source-address rules and resource-growth theorem are reused. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyEncoding
open Machine Foundation.Probability CryptoOracle.Interactive
universe u
variable {State : Type u}

def nativePrograms : List Machine.Program :=
  [OneTimePad.Native.keygenCode, PrivateKeyCopy.code, AuthenticateResponse.code]

def complete (E : FiniteBitEncoding State) :=
  PrivateControllerEncoding.programEncoding.list.prod (EncodedStorage.codeEncoding.prod (frame E))

def codeBits (code : PrivacyMachine.Source.Code) : Nat :=
  2 * ((PrivateControllerEncoding.programEncoding.list).encode nativePrograms).length +
    2 * (EncodedStorage.codeEncoding.encode code).length + 2

def bound (code : PrivacyMachine.Source.Code) (initialAddress initialExtent horizon stateIncrement responseCap : Nat) : Nat :=
  let a := initialAddress + horizon * increment code
  let e := initialExtent + horizon * (stateIncrement + responseCap + 2)
  codeBits code + 32 * a + 144 * PrivacyStorage.bound e + 16 * e + 330

theorem frame_extent_length (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state) (f : PrivacyMachine.Frame State) :
    ((frame E).encode f).length ≤ 32 * maxPc f.control +
      144 * PrivacyStorage.bound (PrivacyStorage.extent stateSize f) +
      16 * PrivacyStorage.extent stateSize f + 330 := by
  have hl := frame_length E stateSize hState f
  have hp := pc_le_twice f.control
  have hc := PrivacyStorage.cells_bound stateSize f
  have hs := ControllerExtent.trace_length f.sourceTrace
  have ht := ControllerExtent.trace_length f.externalTrace
  have hse : ControllerExtent.traceExtent f.sourceTrace ≤ PrivacyStorage.extent stateSize f := by
    simp only [PrivacyStorage.extent]; omega
  have hte : ControllerExtent.traceExtent f.externalTrace ≤ PrivacyStorage.extent stateSize f := by
    simp only [PrivacyStorage.extent]; omega
  omega

theorem encoded_peak (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (code : PrivacyMachine.Source.Code) (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon) (start target : PrivacyMachine.Frame State)
    (hTarget : target ∈ (PrivacyMachine.eval code oracle elapsed start).support) :
    ((complete E).encode (nativePrograms, code, target)).length ≤
      bound code (maxPc start.control) (PrivacyStorage.extent stateSize start) horizon stateIncrement responseCap := by
  have hm : target ∈ (TimedExecution.eval (PrivacyMachine.step code oracle) elapsed start).support := by
    rw [PrivacyMachine.Timing.eval_eq]
    exact hTarget
  have ha := TimedExecution.ResourceGrowth.prefix_bound (PrivacyMachine.step code oracle)
    (fun f => maxPc f.control) (increment code) (max_pc_step code oracle) horizon elapsed hElapsed start target hm
  have he := TimedExecution.ResourceGrowth.prefix_bound (PrivacyMachine.step code oracle)
    (PrivacyStorage.extent stateSize) (stateIncrement + responseCap + 2)
    (PrivacyStorage.envelope stateSize code oracle stateIncrement responseCap hOracle).grows
    horizon elapsed hElapsed start target hm
  have hl := frame_extent_length E stateSize hState target
  have hb := PrivacyStorage.bound_monotone he
  simp only [complete, FiniteBitEncoding.prod_encode_length]
  dsimp only [bound, codeBits]
  omega

theorem bound_polynomial (code : PrivacyMachine.Source.Code)
    {initialAddress initialExtent horizon stateIncrement responseCap : Nat → Nat}
    (hAddress : PolynomiallyBounded initialAddress) (hExtent : PolynomiallyBounded initialExtent)
    (hTime : PolynomiallyBounded horizon) (hIncrement : PolynomiallyBounded stateIncrement)
    (hResponse : PolynomiallyBounded responseCap) :
    PolynomiallyBounded (fun n => bound code (initialAddress n) (initialExtent n)
      (horizon n) (stateIncrement n) (responseCap n)) := by
  have ha := hAddress.add (hTime.mul (PolynomiallyBounded.const (increment code)))
  have he := hExtent.add (hTime.mul ((hIncrement.add hResponse).add (PolynomiallyBounded.const 2)))
  have hb := (((PolynomiallyBounded.const 4).mul (he.mul he)).add
    ((PolynomiallyBounded.const 7).mul he)).add (PolynomiallyBounded.const 2)
  have ht := (((((PolynomiallyBounded.const (codeBits code)).add ((PolynomiallyBounded.const 32).mul ha)).add
    ((PolynomiallyBounded.const 144).mul hb)).add ((PolynomiallyBounded.const 16).mul he)).add
      (PolynomiallyBounded.const 330))
  simpa only [bound, PrivacyStorage.bound, pow_two] using ht

theorem bound_mono_initial (code : PrivacyMachine.Source.Code)
    {a₁ a₂ e₁ e₂ : Nat} (ha : a₁ ≤ a₂) (he : e₁ ≤ e₂) (horizon stateIncrement responseCap : Nat) :
    bound code a₁ e₁ horizon stateIncrement responseCap ≤ bound code a₂ e₂ horizon stateIncrement responseCap := by
  have hx := Nat.add_le_add_right he (horizon * (stateIncrement + responseCap + 2))
  have hb := PrivacyStorage.bound_monotone hx
  dsimp only [bound]
  omega

end Foundation.Symmetric.EncryptThenMAC.PrivacyEncoding
