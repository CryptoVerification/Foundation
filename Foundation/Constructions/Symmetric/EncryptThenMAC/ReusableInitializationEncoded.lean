import Foundation.Constructions.Symmetric.EncryptThenMAC.ReusableInitializationResources
import Foundation.Constructions.Symmetric.EncryptThenMAC.ReusableResponseEncoded
import Foundation.Crypto.Semantics.Oracle.ReusableInitializationEncoding

/-! Faithful whole-code/runtime bit bounds from key generation through any
number of repeated requests. The frozen original caller is encoded as well
as all active state, including the two physical alignment phases. -/
namespace Foundation.Symmetric.EncryptThenMAC.ReusableResponse.Initialized.Encoded
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

def encoding (E : FiniteBitEncoding State) :=
  ReusableInitializationEncoding.runtime PrivacyEncoding.responder E

def phasePc : Control State → Nat
  | .initializing component => ControllerEncoding.initializationPc component
  | .aligning _ => 0
  | .active source => ReusableResponse.Encoded.pc source

def phaseMaxPc : Control State → Nat
  | .initializing component => ControllerEncoding.initializationPc component
  | .aligning _ => 0
  | .active source => ReusableResponse.Encoded.maxPc source

def pc (caller : Configuration State) (c : Control State) := ConfigurationEncoding.pc caller.control + phasePc c
def maxPc (caller : Configuration State) (c : Control State) := max (ConfigurationEncoding.pc caller.control) (phaseMaxPc c)
def traceCount (caller : Configuration State) : Control State → Nat
  | .initializing _ | .aligning _ => caller.reverseTrace.length
  | .active source => caller.reverseTrace.length + ReusableResponse.Encoded.traceCount source

theorem pc_le_three (caller : Configuration State) (c : Control State) : pc caller c ≤ 3 * maxPc caller c := by
  cases c with
  | initializing component => simp only [pc, maxPc, phasePc, phaseMaxPc]; omega
  | aligning tape => simp only [pc, maxPc, phasePc, phaseMaxPc]; omega
  | active source =>
      have hb := ReusableResponse.Encoded.pc_le_twice source
      simp only [pc, maxPc, phasePc, phaseMaxPc]
      omega

variable (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)

include hState in
theorem encoding_length (caller : Configuration State) (c : Control State) :
    ((encoding E).encode (caller, c)).length ≤
      16 * pc caller c + 144 * Resources.cells stateSize caller c + 8 * traceCount caller c + 1024 := by
  have hf := ConfigurationEncoding.frame_length_le E stateSize hState caller
  cases c with
  | initializing component =>
      have hp := ControllerEncoding.initialization_length_le component
      simp only [encoding, ReusableInitializationEncoding.runtime, ReusableInitializationEncoding.control,
        ReusableInitializationEncoding.fields, FiniteBitEncoding.prod_encode_length,
        FiniteBitEncoding.sum_encode_inl_length, pc, phasePc, traceCount,
        Resources.cells, ReusableInitializationStorage.cells, ReusableInitializationStorage.phaseCells]
      omega
  | aligning tape =>
      have hp := Machine.ConfigurationEncoding.tape_length_le tape
      simp only [encoding, ReusableInitializationEncoding.runtime, ReusableInitializationEncoding.control,
        ReusableInitializationEncoding.fields, FiniteBitEncoding.prod_encode_length,
        FiniteBitEncoding.sum_encode_inr_length, FiniteBitEncoding.sum_encode_inl_length,
        pc, phasePc, traceCount, Resources.cells, ReusableInitializationStorage.cells,
        ReusableInitializationStorage.phaseCells]
      omega
  | active source =>
      have hp := ReusableResponse.Encoded.encoding_length E stateSize hState source
      simp only [encoding, ReusableInitializationEncoding.runtime, ReusableInitializationEncoding.control,
        ReusableInitializationEncoding.fields, FiniteBitEncoding.prod_encode_length,
        FiniteBitEncoding.sum_encode_inr_length]
      change ((ReusableResponse.Encoded.encoding E).encode source).length ≤
        16 * ReusableResponse.Encoded.pc source +
        144 * ReusableResponseStorage.cells PrivacyStorage.responderCells stateSize Tape.cells source +
        8 * ReusableResponse.Encoded.traceCount source + 512 at hp
      simp only [ReusableResponse.Encoded.encoding] at hp
      simp only [pc, phasePc, traceCount, Resources.cells, ReusableInitializationStorage.cells,
        ReusableInitializationStorage.phaseCells]
      omega

theorem trace_bound (caller : Configuration State) (c : Control State) :
    traceCount caller c ≤ 3 * Resources.extent stateSize caller c := by
  have ht := ControllerExtent.trace_length caller.reverseTrace
  have hf : ControllerExtent.traceExtent caller.reverseTrace ≤ ControllerExtent.frameExtent stateSize caller := by
    simp only [ControllerExtent.frameExtent]; omega
  cases c with
  | initializing component =>
      simp only [traceCount, Resources.extent, ReusableInitializationStorage.extent]
      omega
  | aligning tape =>
      simp only [traceCount, Resources.extent, ReusableInitializationStorage.extent]
      omega
  | active source =>
      have hp := ReusableResponse.Encoded.trace_bound stateSize source
      change ReusableResponse.Encoded.traceCount source ≤
        2 * ReusableResponseStorage.extent PrivacyStorage.responderExtent stateSize Tape.cells source at hp
      simp only [traceCount, Resources.extent, ReusableInitializationStorage.extent, ReusableInitializationStorage.phaseExtent]
      omega

variable (generator native : Program) (code : Code) (oracle : BitOracle State) (caller : Configuration State)

def addressIncrement (generator native : Program) (code : Code) :=
  generator.addressCap + PrivateKeyCopy.code.addressCap + native.addressCap + EncodedStorage.addressCap code + 1

theorem pc_step (start target : Control State)
    (h : target ∈ (step generator native code oracle caller start).support) :
    maxPc caller target ≤ maxPc caller start + addressIncrement generator native code := by
  cases start with
  | initializing component =>
      cases component with
      | ready key =>
          simp only [step, ReusableResponseInitialization.step, PMF.mem_support_pure_iff] at h
          subst target
          simp only [maxPc, phaseMaxPc, ControllerEncoding.initializationPc]
          omega
      | _ =>
          simp only [step, ReusableResponseInitialization.step, PMF.mem_support_map_iff] at h
          obtain ⟨next, hn, rfl⟩ := h
          have hb := ControllerEncoding.initialization_pc_step generator _ next hn
          simp only [maxPc, phaseMaxPc, addressIncrement]
          omega
  | aligning key =>
      simp only [step, ReusableResponseInitialization.step, PMF.mem_support_pure_iff] at h
      subst target
      simp only [maxPc, phaseMaxPc, ReusableResponse.Encoded.maxPc]
      omega
  | active source =>
      simp only [step, ReusableResponseInitialization.step, PMF.mem_support_map_iff] at h
      obtain ⟨next, hn, rfl⟩ := h
      have hb := ReusableResponse.Encoded.pc_step native code oracle source next hn
      simp only [maxPc, phaseMaxPc, addressIncrement]
      omega

def completeEncoding (E : FiniteBitEncoding State) :=
  PrivateControllerEncoding.programEncoding.prod (PrivateControllerEncoding.programEncoding.prod
    (PrivateControllerEncoding.programEncoding.prod (EncodedStorage.codeEncoding.prod (encoding E))))

def codeBits (generator copy native : Program) (code : Code) :=
  2 * (Program.encode generator).length + ReusableResponse.Encoded.codeBits copy native code + 1

theorem complete_length (generator copy native : Program) (code : Code) (caller : Configuration State) (c : Control State) :
    ((completeEncoding E).encode (generator, copy, native, code, (caller, c))).length =
      codeBits generator copy native code + ((encoding E).encode (caller, c)).length := by
  simp only [completeEncoding, FiniteBitEncoding.prod_encode_length, PrivateControllerEncoding.programEncoding,
    codeBits, ReusableResponse.Encoded.codeBits]
  omega

def bound (generator native : Program) (code : Code)
    (initialPc initialExtent horizon stateIncrement responseCap : Nat) :=
  let p := initialPc + horizon * addressIncrement generator native code
  let e := initialExtent + horizon * (stateIncrement + responseCap + 5)
  codeBits generator PrivateKeyCopy.code native code +
    (48 * p + 144 * (6 * e ^ 2 + 18 * e + 2) + 24 * e + 1024)

theorem bound_mono_initial (generator native : Program) (code : Code)
    {firstPc nextPc firstExtent nextExtent : Nat} (hPc : firstPc ≤ nextPc) (hExtent : firstExtent ≤ nextExtent)
    (horizon stateIncrement responseCap : Nat) :
    bound generator native code firstPc firstExtent horizon stateIncrement responseCap ≤
      bound generator native code nextPc nextExtent horizon stateIncrement responseCap := by
  have hp := Nat.add_le_add_right hPc (horizon * addressIncrement generator native code)
  have he := Nat.add_le_add_right hExtent (horizon * (stateIncrement + responseCap + 5))
  have hq := Nat.pow_le_pow_left he 2
  have hr :
      48 * (firstPc + horizon * addressIncrement generator native code) +
        144 * (6 * (firstExtent + horizon * (stateIncrement + responseCap + 5)) ^ 2 +
          18 * (firstExtent + horizon * (stateIncrement + responseCap + 5)) + 2) +
        24 * (firstExtent + horizon * (stateIncrement + responseCap + 5)) + 1024 ≤
      48 * (nextPc + horizon * addressIncrement generator native code) +
        144 * (6 * (nextExtent + horizon * (stateIncrement + responseCap + 5)) ^ 2 +
          18 * (nextExtent + horizon * (stateIncrement + responseCap + 5)) + 2) +
        24 * (nextExtent + horizon * (stateIncrement + responseCap + 5)) + 1024 := by omega
  exact Nat.add_le_add_left hr (codeBits generator PrivateKeyCopy.code native code)

variable (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)

include hState hOracle in
theorem encoded_peak (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon) (start target : Control State)
    (hTarget : target ∈ (TimedExecution.eval (step generator native code oracle caller) elapsed start).support) :
    ((completeEncoding E).encode (generator, PrivateKeyCopy.code, native, code, (caller, target))).length ≤
      bound generator native code (maxPc caller start) (Resources.extent stateSize caller start) horizon stateIncrement responseCap := by
  have hp := ResourceGrowth.prefix_bound (step generator native code oracle caller) (maxPc caller)
    (addressIncrement generator native code) (pc_step generator native code oracle caller)
    horizon elapsed hElapsed start target hTarget
  have he := ResourceGrowth.prefix_bound (step generator native code oracle caller) (Resources.extent stateSize caller)
    (stateIncrement + responseCap + 5) (Resources.extent_step stateSize caller generator native code oracle stateIncrement responseCap hOracle)
    horizon elapsed hElapsed start target hTarget
  have hc := Resources.cells_bound stateSize caller target
  have hl := encoding_length E stateSize hState caller target
  have hs := pc_le_three caller target
  have ht := trace_bound stateSize caller target
  have hq := Nat.pow_le_pow_left he 2
  have hr : ((encoding E).encode (caller, target)).length ≤
      48 * (maxPc caller start + horizon * addressIncrement generator native code) +
      144 * (6 * (Resources.extent stateSize caller start + horizon * (stateIncrement + responseCap + 5)) ^ 2 +
        18 * (Resources.extent stateSize caller start + horizon * (stateIncrement + responseCap + 5)) + 2) +
      24 * (Resources.extent stateSize caller start + horizon * (stateIncrement + responseCap + 5)) + 1024 := by omega
  rw [complete_length]
  exact Nat.add_le_add_left hr _

theorem bound_polynomial (generator native : Program) (code : Code)
    {initialPc initialExtent horizon stateIncrement responseCap : Nat → Nat}
    (hPc : PolynomiallyBounded initialPc) (hExtent : PolynomiallyBounded initialExtent)
    (hTime : PolynomiallyBounded horizon) (hIncrement : PolynomiallyBounded stateIncrement)
    (hResponse : PolynomiallyBounded responseCap) :
    PolynomiallyBounded (fun n => bound generator native code (initialPc n) (initialExtent n) (horizon n) (stateIncrement n) (responseCap n)) := by
  have hp := hPc.add (hTime.mul (PolynomiallyBounded.const (addressIncrement generator native code)))
  have he := hExtent.add (hTime.mul ((hIncrement.add hResponse).add (PolynomiallyBounded.const 5)))
  have hc := (((PolynomiallyBounded.const 6).mul (he.mul he)).add
    ((PolynomiallyBounded.const 18).mul he)).add (PolynomiallyBounded.const 2)
  have hb := (PolynomiallyBounded.const (codeBits generator PrivateKeyCopy.code native code)).add
    (((((PolynomiallyBounded.const 48).mul hp).add ((PolynomiallyBounded.const 144).mul hc)).add
      ((PolynomiallyBounded.const 24).mul he)).add (PolynomiallyBounded.const 1024))
  simpa only [bound, pow_two] using hb

end Foundation.Symmetric.EncryptThenMAC.ReusableResponse.Initialized.Encoded
