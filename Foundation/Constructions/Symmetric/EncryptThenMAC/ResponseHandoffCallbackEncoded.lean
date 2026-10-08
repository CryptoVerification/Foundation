import Foundation.Constructions.Symmetric.EncryptThenMAC.ResponseHandoffCallbackStorage
import Foundation.Crypto.Semantics.Oracle.ComponentResponseEncoding
import Foundation.Crypto.Semantics.Oracle.PrivateEncodedStorage

/-! Complete code/runtime bit bounds for the combined callback. All saved
metadata, duplicated histories, private tapes and native addresses are kept. -/
namespace Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram.Callback.Encoded
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false

variable {State : Type u}
abbrev Control (State : Type u) := ComponentResponseCallback.Control ResponseHandoff.Control State Tape

def encoding (E : FiniteBitEncoding State) :=
  ComponentResponseEncoding.runtime PrivacyEncoding.responder E Machine.ConfigurationEncoding.tape

def activePc : Control State → Nat
  | .processing component => PrivacyEncoding.responderPc component
  | .delivering frame => PrivateControllerEncoding.callbackPc frame.1

def activeTrace : Control State → Nat
  | .processing _ => 0
  | .delivering frame => PrivateControllerEncoding.callbackTrace frame.1

def maxPc (caller : Machine.Configuration) (c : Control State) := max caller.pc (activePc c)

variable (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)

include hState in
theorem control_length (c : Control State) :
    ((ComponentResponseEncoding.control PrivacyEncoding.responder E Machine.ConfigurationEncoding.tape).encode c).length ≤
      16 * activePc c +
        144 * (match c with
          | .processing component => PrivacyStorage.responderCells component
          | .delivering frame => ControllerStorage.callbackCells stateSize frame.1 + frame.2.cells) +
        8 * activeTrace c + 207 := by
  cases c with
  | processing component =>
      have hc := PrivacyEncoding.responder_length component
      simp only [ComponentResponseEncoding.control, ComponentResponseEncoding.fields,
        FiniteBitEncoding.sum_encode_inl_length, activePc, activeTrace]
      omega
  | delivering frame =>
      rcases frame with ⟨callback, key⟩
      have hc := PrivateControllerEncoding.callback_length_le E stateSize hState callback
      have hk := Machine.ConfigurationEncoding.tape_length_le key
      simp only [ComponentResponseEncoding.control, ComponentResponseEncoding.fields,
        FiniteBitEncoding.sum_encode_inr_length, FiniteBitEncoding.prod_encode_length,
        activePc, activeTrace]
      omega

include hState in
theorem runtime_length (c : Control State) :
    ((encoding E).encode (ComponentResponseEncoding.frame caller state trace request c)).length ≤
      32 * maxPc caller c + 144 * Storage.cells stateSize caller state trace request c +
        16 * Storage.extent stateSize caller state trace request c + 409 := by
  have hf := ConfigurationEncoding.frame_length_le E stateSize hState
    (⟨state, .running caller, trace⟩ : Configuration State)
  have hc := control_length E stateSize hState c
  have ht := ControllerExtent.trace_length trace
  have ha : activeTrace c ≤ Storage.extent stateSize caller state trace request c := by
    cases c with
    | processing component => simp only [activeTrace]; omega
    | delivering frame =>
        cases hh : frame.1 with
        | responding component => simp [activeTrace, hh, PrivateControllerEncoding.callbackTrace]
        | source source =>
            have hs := ControllerExtent.trace_length source.reverseTrace
            simp only [activeTrace, hh, PrivateControllerEncoding.callbackTrace,
              Storage.extent, ComponentResponseStorage.extent, ControllerExtent.callbackExtent,
              ControllerExtent.frameExtent]
            omega
  have hm : ControllerExtent.metadataExtent stateSize caller state trace request ≤
      Storage.extent stateSize caller state trace request c := by
    cases c <;> simp only [Storage.extent, ComponentResponseStorage.extent] <;> omega
  have hs : caller.pc + activePc c ≤ 2 * maxPc caller c := by unfold maxPc; omega
  simp only [ConfigurationEncoding.pc, SourceStorage.cells, SourceStorage.controlCells] at hf
  simp only [encoding, ComponentResponseEncoding.runtime, ComponentResponseEncoding.frame,
    FiniteBitEncoding.prod_encode_length, ConfigurationEncoding.bits, id_eq]
  cases c <;>
    simp only [Storage.cells, ComponentResponseStorage.cells, ComponentResponseStorage.metadataCells,
      Storage.extent, ComponentResponseStorage.extent, ControllerExtent.metadataExtent] at * <;> omega

variable (program : Program) (code : Code) (oracle : BitOracle State)

theorem pc_step (start target : Control State)
    (h : target ∈ (Callback.step program code oracle caller state trace request start).support) :
    maxPc caller target ≤ maxPc caller start +
      (PrivateKeyCopy.code.addressCap + program.addressCap + EncodedStorage.addressCap code + 1) := by
  cases start with
  | processing component =>
      cases hr : Callback.ready component with
      | none =>
          simp only [Callback.step, ComponentResponseCallback.step, hr, PMF.mem_support_map_iff] at h
          obtain ⟨next, hn, rfl⟩ := h
          have hb := ResponseHandoffProgram.pc_step program component next hn
          simp only [maxPc, activePc]
          omega
      | some frame =>
          rcases frame with ⟨machine, retained⟩
          simp only [Callback.step, ComponentResponseCallback.step, hr, PMF.mem_support_pure_iff] at h
          subst target
          have hp : machine.pc = PrivacyEncoding.responderPc component := by
            cases component <;> simp only [Callback.ready, reduceCtorEq] at hr
            split at hr
            · cases hr; rfl
            · contradiction
          simp only [maxPc, activePc, PrivateControllerEncoding.callbackPc, Machine.ControllerEncoding.exportPc, hp]
          omega
  | delivering frame =>
      rcases frame with ⟨callback, retained⟩
      simp only [Callback.step, ComponentResponseCallback.step, framedStep, PMF.map_comp,
        Function.comp_def, PMF.mem_support_map_iff] at h
      obtain ⟨next, hn, rfl⟩ := h
      have hb := PrivateControllerEncoding.callback_pc_step program code oracle caller state trace request callback next hn
      simp only [maxPc, activePc]
      omega

def completeEncoding (E : FiniteBitEncoding State) :=
  PrivateControllerEncoding.programEncoding.prod (PrivateControllerEncoding.programEncoding.prod
    (EncodedStorage.codeEncoding.prod (encoding E)))

def codeBits (copy handler : Program) (code : Code) :=
  2 * (Program.encode copy).length + 2 * (Program.encode handler).length +
    2 * (EncodedStorage.codeEncoding.encode code).length + 3

theorem complete_length (copy handler : Program) (code : Code)
    (runtime : ComponentResponseEncoding.Runtime ResponseHandoff.Control State Tape) :
    ((completeEncoding E).encode (copy, handler, code, runtime)).length =
      codeBits copy handler code + ((encoding E).encode runtime).length := by
  simp only [completeEncoding, FiniteBitEncoding.prod_encode_length,
    PrivateControllerEncoding.programEncoding, codeBits]
  omega

def bound (program : Program) (code : Code)
    (initialPc initialExtent horizon stateIncrement responseCap : Nat) :=
  let pc := initialPc + horizon * (PrivateKeyCopy.code.addressCap + program.addressCap + EncodedStorage.addressCap code + 1)
  let e := initialExtent + horizon * (stateIncrement + responseCap + 3)
  codeBits PrivateKeyCopy.code program code + (32 * pc + 144 * (4 * e ^ 2 + 11 * e + 1) + 16 * e + 409)

variable (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)

include hState hOracle in
theorem encoded_peak (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon) (start target : Control State)
    (hTarget : target ∈ (TimedExecution.eval (Callback.step program code oracle caller state trace request) elapsed start).support) :
    ((completeEncoding E).encode
      (PrivateKeyCopy.code, program, code, ComponentResponseEncoding.frame caller state trace request target)).length ≤
      bound program code (maxPc caller start) (Storage.extent stateSize caller state trace request start)
        horizon stateIncrement responseCap := by
  have hp := ResourceGrowth.prefix_bound (Callback.step program code oracle caller state trace request)
    (maxPc caller) (PrivateKeyCopy.code.addressCap + program.addressCap + EncodedStorage.addressCap code + 1)
    (pc_step caller state trace request program code oracle) horizon elapsed hElapsed start target hTarget
  have he := ResourceGrowth.prefix_bound (Callback.step program code oracle caller state trace request)
    (Storage.extent stateSize caller state trace request) (stateIncrement + responseCap + 3)
    (Storage.extent_step stateSize caller state trace request program code oracle stateIncrement responseCap hOracle)
    horizon elapsed hElapsed start target hTarget
  have hc := Storage.cells_bound stateSize caller state trace request target
  have hl := runtime_length E stateSize hState caller state trace request target
  have hq := Nat.pow_le_pow_left he 2
  have hr : ((encoding E).encode (ComponentResponseEncoding.frame caller state trace request target)).length ≤
      32 * (maxPc caller start + horizon * (PrivateKeyCopy.code.addressCap + program.addressCap + EncodedStorage.addressCap code + 1)) +
      144 * (4 * (Storage.extent stateSize caller state trace request start + horizon * (stateIncrement + responseCap + 3)) ^ 2 +
        11 * (Storage.extent stateSize caller state trace request start + horizon * (stateIncrement + responseCap + 3)) + 1) +
      16 * (Storage.extent stateSize caller state trace request start + horizon * (stateIncrement + responseCap + 3)) + 409 := by omega
  rw [complete_length]
  exact Nat.add_le_add_left hr _

theorem bound_polynomial (program : Program) (code : Code)
    {initialPc initialExtent horizon stateIncrement responseCap : Nat → Nat}
    (hPc : PolynomiallyBounded initialPc) (hExtent : PolynomiallyBounded initialExtent)
    (hTime : PolynomiallyBounded horizon) (hIncrement : PolynomiallyBounded stateIncrement)
    (hResponse : PolynomiallyBounded responseCap) :
    PolynomiallyBounded (fun n => bound program code (initialPc n) (initialExtent n) (horizon n)
      (stateIncrement n) (responseCap n)) := by
  have hp := hPc.add (hTime.mul (PolynomiallyBounded.const
    (PrivateKeyCopy.code.addressCap + program.addressCap + EncodedStorage.addressCap code + 1)))
  have he := hExtent.add (hTime.mul ((hIncrement.add hResponse).add (PolynomiallyBounded.const 3)))
  have hc := (((PolynomiallyBounded.const 4).mul (he.mul he)).add
    ((PolynomiallyBounded.const 11).mul he)).add (PolynomiallyBounded.const 1)
  have hb := (PolynomiallyBounded.const (codeBits PrivateKeyCopy.code program code)).add
    (((((PolynomiallyBounded.const 32).mul hp).add ((PolynomiallyBounded.const 144).mul hc)).add
      ((PolynomiallyBounded.const 16).mul he)).add (PolynomiallyBounded.const 409))
  simpa only [bound, pow_two] using hb

end Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram.Callback.Encoded
