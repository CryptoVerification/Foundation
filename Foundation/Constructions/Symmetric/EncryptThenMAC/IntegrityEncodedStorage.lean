import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityAddresses
import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityStorageExecution
import Foundation.Crypto.Semantics.Oracle.PrivateEncodedStorage

/-! Whole finite-code and state bit bounds for the actual integrity reduction.
The shared source-address rules and resource-growth theorem are reused. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityEncoding
open Machine Foundation.Probability CryptoOracle.Interactive
universe u
variable {State : Type u}

def nativePrograms : List Machine.Program :=
  [OneBitEncryption.Native.keygenCode, OneBitEncryption.Native.encryptionCode]

def complete (E : FiniteBitEncoding State) :=
  PrivateControllerEncoding.programEncoding.list.prod (EncodedStorage.codeEncoding.prod (frame E))

def codeBits (code : IntegrityMachine.SourceCode) : Nat :=
  2 * ((PrivateControllerEncoding.programEncoding.list).encode nativePrograms).length +
    2 * (EncodedStorage.codeEncoding.encode code).length + 2

def bound (code : IntegrityMachine.SourceCode) (initialScalar initialExtent horizon stateIncrement responseCap : Nat) : Nat :=
  let a := initialScalar + horizon * increment code
  let e := initialExtent + horizon * (stateIncrement + responseCap + 2)
  codeBits code + 32 * a + 144 * IntegrityStorage.bound e + 16 * e + 522

theorem frame_extent_length (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state) (f : IntegrityMachine.Frame State) :
    ((frame E).encode f).length ≤ 32 * maxScalar f.control +
      144 * IntegrityStorage.bound (IntegrityStorage.extent stateSize f) +
      16 * IntegrityStorage.extent stateSize f + 522 := by
  have hl := frame_length E stateSize hState f
  have hp := scalar_le_twice f.control
  have hc := IntegrityStorage.cells_bound stateSize f
  have hs := ControllerExtent.trace_length f.sourceTrace
  have ht := ControllerExtent.trace_length (IntegrityStorage.signingTrace f.signingTrace)
  have hse : ControllerExtent.traceExtent f.sourceTrace ≤ IntegrityStorage.extent stateSize f := by
    simp only [IntegrityStorage.extent]; omega
  have hte : ControllerExtent.traceExtent (IntegrityStorage.signingTrace f.signingTrace) ≤ IntegrityStorage.extent stateSize f := by
    simp only [IntegrityStorage.extent]; omega
  simp only [IntegrityStorage.signingTrace, List.length_map] at ht hte
  omega

theorem encoded_peak (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (code : IntegrityMachine.SourceCode) (oracle : State → Bool → PMF (State × List Bool)) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon) (start target : IntegrityMachine.Frame State)
    (hTarget : target ∈ (IntegrityMachine.eval code oracle elapsed start).support) :
    ((complete E).encode (nativePrograms, code, target)).length ≤
      bound code (maxScalar start.control) (IntegrityStorage.extent stateSize start) horizon stateIncrement responseCap := by
  have hm : target ∈ (TimedExecution.eval (IntegrityMachine.step code oracle) elapsed start).support := hTarget
  have ha := TimedExecution.ResourceGrowth.prefix_bound (IntegrityMachine.step code oracle)
    (fun f => maxScalar f.control) (increment code) (max_scalar_step code oracle) horizon elapsed hElapsed start target hm
  have he := TimedExecution.ResourceGrowth.prefix_bound (IntegrityMachine.step code oracle)
    (IntegrityStorage.extent stateSize) (stateIncrement + responseCap + 2)
    (IntegrityStorage.envelope stateSize code oracle stateIncrement responseCap hOracle).grows
    horizon elapsed hElapsed start target hm
  have hl := frame_extent_length E stateSize hState target
  have hb := IntegrityStorage.bound_monotone he
  simp only [complete, FiniteBitEncoding.prod_encode_length]
  dsimp only [bound, codeBits]
  omega

theorem bound_polynomial (code : IntegrityMachine.SourceCode)
    {initialScalar initialExtent horizon stateIncrement responseCap : Nat → Nat}
    (hScalar : PolynomiallyBounded initialScalar) (hExtent : PolynomiallyBounded initialExtent)
    (hTime : PolynomiallyBounded horizon) (hIncrement : PolynomiallyBounded stateIncrement)
    (hResponse : PolynomiallyBounded responseCap) :
    PolynomiallyBounded (fun n => bound code (initialScalar n) (initialExtent n)
      (horizon n) (stateIncrement n) (responseCap n)) := by
  have ha := hScalar.add (hTime.mul (PolynomiallyBounded.const (increment code)))
  have he := hExtent.add (hTime.mul ((hIncrement.add hResponse).add (PolynomiallyBounded.const 2)))
  have hb := (((PolynomiallyBounded.const 4).mul (he.mul he)).add
    ((PolynomiallyBounded.const 7).mul he)).add (PolynomiallyBounded.const 2)
  have ht := (((((PolynomiallyBounded.const (codeBits code)).add ((PolynomiallyBounded.const 32).mul ha)).add
    ((PolynomiallyBounded.const 144).mul hb)).add ((PolynomiallyBounded.const 16).mul he)).add
      (PolynomiallyBounded.const 522))
  simpa only [bound, IntegrityStorage.bound, pow_two] using ht

theorem bound_mono_initial (code : IntegrityMachine.SourceCode)
    {a₁ a₂ e₁ e₂ : Nat} (ha : a₁ ≤ a₂) (he : e₁ ≤ e₂) (horizon stateIncrement responseCap : Nat) :
    bound code a₁ e₁ horizon stateIncrement responseCap ≤ bound code a₂ e₂ horizon stateIncrement responseCap := by
  have hx := Nat.add_le_add_right he (horizon * (stateIncrement + responseCap + 2))
  have hb := IntegrityStorage.bound_monotone hx
  dsimp only [bound]
  omega

end Foundation.Symmetric.EncryptThenMAC.IntegrityEncoding
