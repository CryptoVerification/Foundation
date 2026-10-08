import Foundation.Crypto.Semantics.Machine.ControllerEncoding
import Foundation.Crypto.Semantics.Oracle.ConfigurationEncoding

/-! Complete encodings of the private-key source and callback controllers.
Saved callers, private tapes, requests and each retained transcript copy are
encoded separately. Size bounds explicitly retain native control addresses. -/
namespace CryptoOracle.Interactive.PrivateControllerEncoding
open Machine Foundation.Probability
universe u
variable {State : Type u} (E : FiniteBitEncoding State)

def callbackFields := ControllerEncoding.responseExport.sum (ConfigurationEncoding.frame E)
def callback : FiniteBitEncoding (NativeCallback.Control State) where
  encode := fun c => (callbackFields E).encode (match c with | .responding component => .inl component | .source frame => .inr frame)
  decode := fun raw => ((callbackFields E).decode raw).map fun f => match f with | .inl component => .responding component | .inr frame => .source frame
  decode_encode := by intro c; cases c <;> simp [(callbackFields E).decode_encode]

def callbackPc : NativeCallback.Control State → Nat
  | .responding component => ControllerEncoding.exportPc component
  | .source frame => ConfigurationEncoding.pc frame.control

def callbackTrace : NativeCallback.Control State → Nat
  | .responding _ => 0
  | .source frame => frame.reverseTrace.length

theorem callback_length_le (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state) (c : NativeCallback.Control State) :
    ((callback E).encode c).length ≤ 8 * callbackPc c +
      72 * ControllerStorage.callbackCells stateSize c + 4 * callbackTrace c + 101 := by
  cases c with
  | responding component =>
      have hc := ControllerEncoding.export_length_le component
      simp only [callback, callbackFields, FiniteBitEncoding.sum_encode_inl_length,
        callbackPc, callbackTrace, ControllerStorage.callbackCells]
      omega
  | source frame =>
      have hf := ConfigurationEncoding.frame_length_le E stateSize hState frame
      simp only [callback, callbackFields, FiniteBitEncoding.sum_encode_inr_length,
        callbackPc, callbackTrace, ControllerStorage.callbackCells]
      omega

def checkedFields := ControllerEncoding.check.sum
  ((ControllerEncoding.tape.prod (ControllerEncoding.tape.prod ControllerEncoding.responseExport)).sum
    ((ControllerEncoding.tape.prod (ControllerEncoding.tape.prod ControllerEncoding.packet)).sum
      (ControllerEncoding.tape.prod (ControllerEncoding.tape.prod (callback E)))))

def checked : FiniteBitEncoding (CheckedCallback.Control State) where
  encode := fun c => (checkedFields E).encode (match c with
    | .preparing preparation => .inl preparation
    | .computing first second component => .inr (.inl (first, second, component))
    | .tagging first second packet => .inr (.inr (.inl (first, second, packet)))
    | .calling first second result => .inr (.inr (.inr (first, second, result))))
  decode := fun raw => ((checkedFields E).decode raw).map fun f => match f with
    | .inl preparation => .preparing preparation
    | .inr (.inl (first, second, component)) => .computing first second component
    | .inr (.inr (.inl (first, second, packet))) => .tagging first second packet
    | .inr (.inr (.inr (first, second, result))) => .calling first second result
  decode_encode := by intro c; cases c <;> simp [(checkedFields E).decode_encode]

def checkedPc : CheckedCallback.Control State → Nat
  | .computing _ _ component => ControllerEncoding.exportPc component
  | .calling _ _ result => callbackPc result
  | _ => 0

def checkedTrace : CheckedCallback.Control State → Nat
  | .calling _ _ result => callbackTrace result
  | _ => 0

theorem checked_length_le (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state) (c : CheckedCallback.Control State) :
    ((checked E).encode c).length ≤ 8 * checkedPc c +
      72 * ControllerStorage.checkedCells stateSize c + 4 * checkedTrace c + 128 := by
  cases c with
  | preparing preparation =>
      have hp := ControllerEncoding.check_length_le preparation
      simp only [checked, checkedFields, FiniteBitEncoding.sum_encode_inl_length,
        checkedPc, checkedTrace, ControllerStorage.checkedCells]
      omega
  | computing first second component =>
      have ha := Machine.ConfigurationEncoding.tape_length_le first
      have hb := Machine.ConfigurationEncoding.tape_length_le second
      have hc := ControllerEncoding.export_length_le component
      simp only [checked, checkedFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.prod_encode_length,
        ControllerEncoding.tape, checkedPc, checkedTrace, ControllerStorage.checkedCells]
      omega
  | tagging first second response =>
      have ha := Machine.ConfigurationEncoding.tape_length_le first
      have hb := Machine.ConfigurationEncoding.tape_length_le second
      have hc := ControllerEncoding.packet_length_le response
      simp only [checked, checkedFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.prod_encode_length,
        ControllerEncoding.tape, checkedPc, checkedTrace, ControllerStorage.checkedCells]
      omega
  | calling first second result =>
      have ha := Machine.ConfigurationEncoding.tape_length_le first
      have hb := Machine.ConfigurationEncoding.tape_length_le second
      have hc := callback_length_le E stateSize hState result
      simp only [checked, checkedFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, ControllerEncoding.tape,
        checkedPc, checkedTrace, ControllerStorage.checkedCells]
      omega

def sourceFields :=
  (Machine.ConfigurationEncoding.bit.prod (ControllerEncoding.tape.prod (ConfigurationEncoding.frame E))).sum
    (Machine.ConfigurationEncoding.bit.prod (Machine.ConfigurationEncoding.configuration.prod
      (E.prod (ConfigurationEncoding.trace.prod (ConfigurationEncoding.bits.prod (checked E))))))

def source : FiniteBitEncoding (OneUseSource.Control State) where
  encode := fun c => (sourceFields E).encode (match c with
    | .source used key frame => .inl (used, key, frame)
    | .handling used saved state trace request handler => .inr (used, saved, state, trace, request, handler))
  decode := fun raw => ((sourceFields E).decode raw).map fun f => match f with
    | .inl (used, key, frame) => .source used key frame
    | .inr (used, saved, state, trace, request, handler) => .handling used saved state trace request handler
  decode_encode := by intro c; cases c <;> simp [(sourceFields E).decode_encode]

def sourcePc : OneUseSource.Control State → Nat
  | .source _ _ frame => ConfigurationEncoding.pc frame.control
  | .handling _ saved _ _ _ handler => saved.pc + checkedPc handler

def sourceTrace : OneUseSource.Control State → Nat
  | .source _ _ frame => frame.reverseTrace.length
  | .handling _ _ _ trace _ handler => trace.length + checkedTrace handler

theorem source_length_le (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state) (c : OneUseSource.Control State) :
    ((source E).encode c).length ≤ 8 * sourcePc c +
      72 * ControllerStorage.sourceCells stateSize c + 8 * sourceTrace c + 192 := by
  cases c with
  | source used key frame =>
      have hk := Machine.ConfigurationEncoding.tape_length_le key
      have hf := ConfigurationEncoding.frame_length_le E stateSize hState frame
      simp only [source, sourceFields, FiniteBitEncoding.sum_encode_inl_length,
        FiniteBitEncoding.prod_encode_length, Machine.ConfigurationEncoding.bit,
        List.length_singleton, ControllerEncoding.tape, sourcePc, sourceTrace, ControllerStorage.sourceCells]
      omega
  | handling used saved state trace request handler =>
      have hm := Machine.ConfigurationEncoding.configuration_length_le saved
      have hs := hState state
      have ht := ConfigurationEncoding.trace_length_le trace
      have hh := checked_length_le E stateSize hState handler
      simp only [source, sourceFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, Machine.ConfigurationEncoding.bit,
        List.length_singleton, ConfigurationEncoding.bits, id_eq,
        sourcePc, sourceTrace, ControllerStorage.sourceCells]
      omega

/-- During key generation the suspended caller is retained as runtime data.
This representation preserves that caller instead of treating it as free code. -/
abbrev InitializationRuntime (State : Type u) :=
  (Configuration State × PrivateInitialization.Control) ⊕ OneUseSource.Control State

def initializationRuntime : FiniteBitEncoding (InitializationRuntime State) :=
  ((ConfigurationEncoding.frame E).prod ControllerEncoding.initialization).sum (source E)

def runtime (caller : Configuration State) : OneUseInitialization.Control State → InitializationRuntime State
  | .initializing component => .inl (caller, component)
  | .active component => .inr component

def initializationPc (caller : Configuration State) : OneUseInitialization.Control State → Nat
  | .initializing component => ConfigurationEncoding.pc caller.control + ControllerEncoding.initializationPc component
  | .active component => sourcePc component

def initializationTrace (caller : Configuration State) : OneUseInitialization.Control State → Nat
  | .initializing _ => caller.reverseTrace.length
  | .active component => sourceTrace component

theorem initialization_length_le (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (caller : Configuration State) (c : OneUseInitialization.Control State) :
    ((initializationRuntime E).encode (runtime caller c)).length ≤
      16 * initializationPc caller c + 144 * ControllerStorage.initializationCells stateSize caller c +
        8 * initializationTrace caller c + 256 := by
  cases c with
  | initializing component =>
      have hf := ConfigurationEncoding.frame_length_le E stateSize hState caller
      have hc := ControllerEncoding.initialization_length_le component
      simp only [initializationRuntime, runtime, FiniteBitEncoding.sum_encode_inl_length,
        FiniteBitEncoding.prod_encode_length, initializationPc, initializationTrace, ControllerStorage.initializationCells]
      omega
  | active component =>
      have hs := source_length_le E stateSize hState component
      simp only [initializationRuntime, runtime, FiniteBitEncoding.sum_encode_inr_length,
        initializationPc, initializationTrace, ControllerStorage.initializationCells]
      omega

theorem callback_trace_le (stateSize : State → Nat) (c : NativeCallback.Control State) :
    callbackTrace c ≤ ControllerExtent.callbackExtent stateSize c := by
  cases c with
  | responding component => simp [callbackTrace]
  | source frame =>
      have ht := ControllerExtent.trace_length frame.reverseTrace
      simp only [callbackTrace, ControllerExtent.callbackExtent, ControllerExtent.frameExtent]
      omega

theorem checked_trace_le (stateSize : State → Nat) (c : CheckedCallback.Control State) :
    checkedTrace c ≤ ControllerExtent.checkedExtent stateSize c := by
  cases c <;> simp only [checkedTrace]
  all_goals try exact Nat.zero_le _
  case calling first second result =>
    have ht := callback_trace_le stateSize result
    simp only [ControllerExtent.checkedExtent]
    omega

theorem source_trace_le (stateSize : State → Nat) (c : OneUseSource.Control State) :
    sourceTrace c ≤ 2 * ControllerExtent.sourceExtent stateSize c := by
  cases c with
  | source used key frame =>
      have ht := ControllerExtent.trace_length frame.reverseTrace
      simp only [sourceTrace, ControllerExtent.sourceExtent, ControllerExtent.frameExtent]
      omega
  | handling used saved state trace request handler =>
      have ht := ControllerExtent.trace_length trace
      have hh := checked_trace_le stateSize handler
      simp only [sourceTrace, ControllerExtent.sourceExtent]
      omega

theorem initialization_trace_le (stateSize : State → Nat) (caller : Configuration State)
    (c : OneUseInitialization.Control State) :
    initializationTrace caller c ≤ 2 * ControllerExtent.initializationExtent stateSize caller c := by
  cases c with
  | initializing component =>
      have ht := ControllerExtent.trace_length caller.reverseTrace
      simp only [initializationTrace, ControllerExtent.initializationExtent, ControllerExtent.frameExtent]
      omega
  | active component => exact source_trace_le stateSize component

theorem initialization_extent_length_le (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (caller : Configuration State) (c : OneUseInitialization.Control State) :
    ((initializationRuntime E).encode (runtime caller c)).length ≤
      16 * initializationPc caller c +
        144 * (4 * (ControllerExtent.initializationExtent stateSize caller c) ^ 2 +
          11 * ControllerExtent.initializationExtent stateSize caller c + 2) +
        16 * ControllerExtent.initializationExtent stateSize caller c + 256 := by
  have hl := initialization_length_le E stateSize hState caller c
  have hc := ControllerExtent.initialization_cells stateSize caller c
  have ht := initialization_trace_le stateSize caller c
  omega

end CryptoOracle.Interactive.PrivateControllerEncoding
