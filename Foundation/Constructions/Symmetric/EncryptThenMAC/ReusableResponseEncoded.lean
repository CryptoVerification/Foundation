import Foundation.Constructions.Symmetric.EncryptThenMAC.ReusableResponseResources
import Foundation.Crypto.Semantics.Oracle.ReusableResponseEncoding
import Foundation.Crypto.Semantics.Oracle.PrivateEncodedStorage

/-! Whole finite-code/runtime bit bounds across arbitrary repeated requests.
Bounds follow the real step relation, including request capture and release. -/
namespace Foundation.Symmetric.EncryptThenMAC.ReusableResponse.Encoded
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

def encoding (E : FiniteBitEncoding State) :=
  ReusableResponseEncoding.control PrivacyEncoding.responder E Machine.ConfigurationEncoding.tape

def pc : ReusableResponse.Control State → Nat
  | .source _ frame => ConfigurationEncoding.pc frame.control
  | .processing caller _ _ _ component => caller.pc + PrivacyEncoding.responderPc component
  | .calling caller _ _ _ callback _ => caller.pc + PrivateControllerEncoding.callbackPc callback

def maxPc : ReusableResponse.Control State → Nat
  | .source _ frame => ConfigurationEncoding.pc frame.control
  | .processing caller _ _ _ component => max caller.pc (PrivacyEncoding.responderPc component)
  | .calling caller _ _ _ callback _ => max caller.pc (PrivateControllerEncoding.callbackPc callback)

def traceCount : ReusableResponse.Control State → Nat
  | .source _ frame => frame.reverseTrace.length
  | .processing _ _ trace _ _ => trace.length
  | .calling _ _ trace _ callback _ => trace.length + PrivateControllerEncoding.callbackTrace callback

theorem pc_le_twice (c : ReusableResponse.Control State) : pc c ≤ 2 * maxPc c := by
  cases c <;> simp only [pc, maxPc] <;> omega

variable (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)

include hState in
theorem encoding_length (c : ReusableResponse.Control State) :
    ((encoding E).encode c).length ≤ 16 * pc c + 144 * Resources.cells stateSize c + 8 * traceCount c + 512 := by
  cases c with
  | source retained frame =>
      have hk := Machine.ConfigurationEncoding.tape_length_le retained
      have hf := ConfigurationEncoding.frame_length_le E stateSize hState frame
      simp only [encoding, ReusableResponseEncoding.control, ReusableResponseEncoding.fields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.prod_encode_length,
        pc, traceCount, Resources.cells, ReusableResponseStorage.cells]
      omega
  | processing caller state trace request component =>
      have hm := Machine.ConfigurationEncoding.configuration_length_le caller
      have hs := hState state
      have ht := ConfigurationEncoding.trace_length_le trace
      have hc := PrivacyEncoding.responder_length component
      simp only [encoding, ReusableResponseEncoding.control, ReusableResponseEncoding.fields,
        ReusableResponseEncoding.metadata, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.prod_encode_length,
        ConfigurationEncoding.bits, id_eq, pc, traceCount, Resources.cells,
        ReusableResponseStorage.cells, ComponentResponseStorage.metadataCells]
      omega
  | calling caller state trace request callback retained =>
      have hm := Machine.ConfigurationEncoding.configuration_length_le caller
      have hs := hState state
      have ht := ConfigurationEncoding.trace_length_le trace
      have hc := PrivateControllerEncoding.callback_length_le E stateSize hState callback
      have hk := Machine.ConfigurationEncoding.tape_length_le retained
      simp only [encoding, ReusableResponseEncoding.control, ReusableResponseEncoding.fields,
        ReusableResponseEncoding.metadata, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, ConfigurationEncoding.bits, id_eq, pc, traceCount,
        Resources.cells, ReusableResponseStorage.cells, ComponentResponseStorage.metadataCells]
      omega

theorem trace_bound (c : ReusableResponse.Control State) : traceCount c ≤ 2 * Resources.extent stateSize c := by
  cases c with
  | source retained frame =>
      have ht := ControllerExtent.trace_length frame.reverseTrace
      simp only [traceCount, Resources.extent, ReusableResponseStorage.extent, ControllerExtent.frameExtent]
      omega
  | processing caller state trace request component =>
      have ht := ControllerExtent.trace_length trace
      simp only [traceCount, Resources.extent, ReusableResponseStorage.extent, ControllerExtent.metadataExtent]
      omega
  | calling caller state trace request callback retained =>
      have ht := ControllerExtent.trace_length trace
      cases callback with
      | responding component =>
          simp only [traceCount, PrivateControllerEncoding.callbackTrace, Resources.extent,
            ReusableResponseStorage.extent, ControllerExtent.metadataExtent]
          omega
      | source frame =>
          have hs := ControllerExtent.trace_length frame.reverseTrace
          simp only [traceCount, PrivateControllerEncoding.callbackTrace, Resources.extent,
            ReusableResponseStorage.extent, ControllerExtent.metadataExtent,
            ControllerExtent.callbackExtent, ControllerExtent.frameExtent]
          omega

variable (program : Program) (code : Code) (oracle : BitOracle State)

theorem pc_step (start target : ReusableResponse.Control State)
    (h : target ∈ (ReusableResponse.step program code oracle start).support) :
    maxPc target ≤ maxPc start + (PrivateKeyCopy.code.addressCap + program.addressCap + EncodedStorage.addressCap code + 1) := by
  cases start with
  | source retained frame =>
      rcases frame with ⟨state, control, trace⟩
      cases control with
      | awaiting caller request =>
          simp only [ReusableResponse.step, ReusableResponseSource.step, PMF.mem_support_pure_iff] at h
          subst target
          simp [maxPc, ConfigurationEncoding.pc, ReusableResponse.begin, PrivacyEncoding.responderPc]
      | _ =>
          simp only [ReusableResponse.step, ReusableResponseSource.step, PMF.mem_support_map_iff] at h
          obtain ⟨next, hn, rfl⟩ := h
          have hb := EncodedStorage.pc_step code oracle _ next hn
          dsimp only at hb
          simp only [maxPc]
          omega
  | processing caller state trace request component =>
      cases hr : ResponseHandoffProgram.Callback.ready component with
      | none =>
          simp only [ReusableResponse.step, ReusableResponseSource.step, hr, PMF.mem_support_map_iff] at h
          obtain ⟨next, hn, rfl⟩ := h
          have hb := ResponseHandoffProgram.pc_step program component next hn
          simp only [maxPc]
          omega
      | some frame =>
          rcases frame with ⟨machine, retained⟩
          simp only [ReusableResponse.step, ReusableResponseSource.step, hr, PMF.mem_support_pure_iff] at h
          subst target
          have hp : machine.pc = PrivacyEncoding.responderPc component := by
            cases component <;> simp only [ResponseHandoffProgram.Callback.ready, reduceCtorEq] at hr
            split at hr
            · cases hr; rfl
            · contradiction
          simp only [maxPc, PrivateControllerEncoding.callbackPc, Machine.ControllerEncoding.exportPc, hp]
          omega
  | calling caller state trace request callback retained =>
      cases callback with
      | responding component =>
          simp only [ReusableResponse.step, ReusableResponseSource.step, PMF.mem_support_map_iff] at h
          obtain ⟨next, hn, rfl⟩ := h
          have hb := PrivateControllerEncoding.callback_pc_step program code oracle caller state trace request (.responding component) next hn
          simp only [maxPc]
          omega
      | source frame =>
          rcases frame with ⟨state, control, trace⟩
          cases control with
          | running machine =>
              simp only [ReusableResponse.step, ReusableResponseSource.step, PMF.mem_support_pure_iff] at h
              subst target
              simp only [maxPc, PrivateControllerEncoding.callbackPc, ConfigurationEncoding.pc]
              omega
          | _ =>
              simp only [ReusableResponse.step, ReusableResponseSource.step, NativeCallback.step,
                PMF.map_comp, Function.comp_def, PMF.mem_support_map_iff] at h
              obtain ⟨next, hn, rfl⟩ := h
              have hb := EncodedStorage.pc_step code oracle _ next hn
              dsimp only at hb
              simp only [maxPc, PrivateControllerEncoding.callbackPc]
              omega

def completeEncoding (E : FiniteBitEncoding State) :=
  PrivateControllerEncoding.programEncoding.prod (PrivateControllerEncoding.programEncoding.prod
    (EncodedStorage.codeEncoding.prod (encoding E)))

def codeBits (copy handler : Program) (code : Code) :=
  2 * (Program.encode copy).length + 2 * (Program.encode handler).length +
    2 * (EncodedStorage.codeEncoding.encode code).length + 3

theorem complete_length (copy handler : Program) (code : Code) (c : ReusableResponse.Control State) :
    ((completeEncoding E).encode (copy, handler, code, c)).length = codeBits copy handler code + ((encoding E).encode c).length := by
  simp only [completeEncoding, FiniteBitEncoding.prod_encode_length, PrivateControllerEncoding.programEncoding, codeBits]
  omega

def bound (program : Program) (code : Code) (initialPc initialExtent horizon stateIncrement responseCap : Nat) :=
  let p := initialPc + horizon * (PrivateKeyCopy.code.addressCap + program.addressCap + EncodedStorage.addressCap code + 1)
  let e := initialExtent + horizon * (stateIncrement + responseCap + 4)
  codeBits PrivateKeyCopy.code program code + (32 * p + 144 * (4 * e ^ 2 + 13 * e + 1) + 16 * e + 512)

variable (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)

include hState hOracle in
theorem encoded_peak (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon) (start target : ReusableResponse.Control State)
    (hTarget : target ∈ (TimedExecution.eval (ReusableResponse.step program code oracle) elapsed start).support) :
    ((completeEncoding E).encode (PrivateKeyCopy.code, program, code, target)).length ≤
      bound program code (maxPc start) (Resources.extent stateSize start) horizon stateIncrement responseCap := by
  have hp := ResourceGrowth.prefix_bound (ReusableResponse.step program code oracle) maxPc
    (PrivateKeyCopy.code.addressCap + program.addressCap + EncodedStorage.addressCap code + 1)
    (pc_step program code oracle) horizon elapsed hElapsed start target hTarget
  have he := ResourceGrowth.prefix_bound (ReusableResponse.step program code oracle) (Resources.extent stateSize)
    (stateIncrement + responseCap + 4) (Resources.extent_step stateSize program code oracle stateIncrement responseCap hOracle)
    horizon elapsed hElapsed start target hTarget
  have hc := Resources.cells_bound stateSize target
  have hl := encoding_length E stateSize hState target
  have hs := pc_le_twice target
  have ht := trace_bound stateSize target
  have hq := Nat.pow_le_pow_left he 2
  have hr : ((encoding E).encode target).length ≤
      32 * (maxPc start + horizon * (PrivateKeyCopy.code.addressCap + program.addressCap + EncodedStorage.addressCap code + 1)) +
      144 * (4 * (Resources.extent stateSize start + horizon * (stateIncrement + responseCap + 4)) ^ 2 +
        13 * (Resources.extent stateSize start + horizon * (stateIncrement + responseCap + 4)) + 1) +
      16 * (Resources.extent stateSize start + horizon * (stateIncrement + responseCap + 4)) + 512 := by omega
  rw [complete_length]
  exact Nat.add_le_add_left hr _

theorem bound_polynomial (program : Program) (code : Code) {initialPc initialExtent horizon stateIncrement responseCap : Nat → Nat}
    (hPc : PolynomiallyBounded initialPc) (hExtent : PolynomiallyBounded initialExtent)
    (hTime : PolynomiallyBounded horizon) (hIncrement : PolynomiallyBounded stateIncrement)
    (hResponse : PolynomiallyBounded responseCap) :
    PolynomiallyBounded (fun n => bound program code (initialPc n) (initialExtent n) (horizon n) (stateIncrement n) (responseCap n)) := by
  have hp := hPc.add (hTime.mul (PolynomiallyBounded.const
    (PrivateKeyCopy.code.addressCap + program.addressCap + EncodedStorage.addressCap code + 1)))
  have he := hExtent.add (hTime.mul ((hIncrement.add hResponse).add (PolynomiallyBounded.const 4)))
  have hc := (((PolynomiallyBounded.const 4).mul (he.mul he)).add
    ((PolynomiallyBounded.const 13).mul he)).add (PolynomiallyBounded.const 1)
  have hb := (PolynomiallyBounded.const (codeBits PrivateKeyCopy.code program code)).add
    (((((PolynomiallyBounded.const 32).mul hp).add ((PolynomiallyBounded.const 144).mul hc)).add
      ((PolynomiallyBounded.const 16).mul he)).add (PolynomiallyBounded.const 512))
  simpa only [bound, pow_two] using hb

end Foundation.Symmetric.EncryptThenMAC.ReusableResponse.Encoded
