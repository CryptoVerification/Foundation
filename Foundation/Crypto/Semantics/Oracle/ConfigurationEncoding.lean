import Foundation.Crypto.Semantics.Machine.ListEncoding
import Foundation.Crypto.Semantics.Machine.ConfigurationEncoding
import Foundation.Crypto.Semantics.Oracle.ControllerExtent

/-! Faithful representations of the entire public interactive controller and
external state. An external-state codec is supplied explicitly. Empty request
and response events remain distinct; transcript entry overhead is counted. -/
namespace CryptoOracle.Interactive.ConfigurationEncoding
open Machine Foundation.Probability
universe u

def bits : FiniteBitEncoding (List Bool) := ⟨id, some, fun _ => rfl⟩
def native := Machine.ConfigurationEncoding.configuration
def tape := Machine.ConfigurationEncoding.tape
def sending := native.prod (tape.prod bits)
def reversing := native.prod (bits.prod bits)
def awaiting := native.prod bits
def loading := native.prod (bits.prod tape)
def rewinding := native.prod tape
def controlFields := native.sum (sending.sum (reversing.sum (awaiting.sum
  (loading.sum (loading.sum (rewinding.sum Machine.ConfigurationEncoding.bit))))))

def control : FiniteBitEncoding Control where
  encode := fun c => controlFields.encode (match c with
    | .running machine => .inl machine
    | .sending machine store acc => .inr (.inl (machine, store, acc))
    | .reversing machine rest request => .inr (.inr (.inl (machine, rest, request)))
    | .awaiting machine request => .inr (.inr (.inr (.inl (machine, request))))
    | .loading machine rest store => .inr (.inr (.inr (.inr (.inl (machine, rest, store)))))
    | .advancing machine rest store => .inr (.inr (.inr (.inr (.inr (.inl (machine, rest, store))))))
    | .rewinding machine store => .inr (.inr (.inr (.inr (.inr (.inr (.inl (machine, store)))))))
    | .finished result => .inr (.inr (.inr (.inr (.inr (.inr (.inr result)))))))
  decode := fun raw => (controlFields.decode raw).map fun fields => match fields with
    | .inl machine => .running machine
    | .inr (.inl (machine, store, acc)) => .sending machine store acc
    | .inr (.inr (.inl (machine, rest, request))) => .reversing machine rest request
    | .inr (.inr (.inr (.inl (machine, request)))) => .awaiting machine request
    | .inr (.inr (.inr (.inr (.inl (machine, rest, store))))) => .loading machine rest store
    | .inr (.inr (.inr (.inr (.inr (.inl (machine, rest, store)))))) => .advancing machine rest store
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl (machine, store))))))) => .rewinding machine store
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr result)))))) => .finished result
  decode_encode := by intro c; cases c <;> simp [controlFields.decode_encode]

def pc : Control → Nat
  | .running machine | .sending machine _ _ | .reversing machine _ _ | .awaiting machine _
  | .loading machine _ _ | .advancing machine _ _ | .rewinding machine _ => machine.pc
  | .finished _ => 0

theorem control_length_le (c : Control) :
    (control.encode c).length ≤ 4 * pc c + 36 * SourceStorage.controlCells c + 48 := by
  cases c with
  | running machine =>
      have hm := Machine.ConfigurationEncoding.configuration_length_le machine
      simp only [control, controlFields, FiniteBitEncoding.sum_encode_inl_length,
        native, pc, SourceStorage.controlCells]
      omega
  | sending machine store acc =>
      have hm := Machine.ConfigurationEncoding.configuration_length_le machine
      have ht := Machine.ConfigurationEncoding.tape_length_le store
      simp only [control, controlFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, sending, FiniteBitEncoding.prod_encode_length,
        native, tape, bits, id_eq, pc, SourceStorage.controlCells]
      omega
  | reversing machine rest request =>
      have hm := Machine.ConfigurationEncoding.configuration_length_le machine
      simp only [control, controlFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, reversing, FiniteBitEncoding.prod_encode_length,
        native, bits, id_eq, pc, SourceStorage.controlCells]
      omega
  | awaiting machine request =>
      have hm := Machine.ConfigurationEncoding.configuration_length_le machine
      simp only [control, controlFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, awaiting, FiniteBitEncoding.prod_encode_length,
        native, bits, id_eq, pc, SourceStorage.controlCells]
      omega
  | loading machine rest store =>
      have hm := Machine.ConfigurationEncoding.configuration_length_le machine
      have ht := Machine.ConfigurationEncoding.tape_length_le store
      simp only [control, controlFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, loading, FiniteBitEncoding.prod_encode_length,
        native, tape, bits, id_eq, pc, SourceStorage.controlCells]
      omega
  | advancing machine rest store =>
      have hm := Machine.ConfigurationEncoding.configuration_length_le machine
      have ht := Machine.ConfigurationEncoding.tape_length_le store
      simp only [control, controlFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, loading, FiniteBitEncoding.prod_encode_length,
        native, tape, bits, id_eq, pc, SourceStorage.controlCells]
      omega
  | rewinding machine store =>
      have hm := Machine.ConfigurationEncoding.configuration_length_le machine
      have ht := Machine.ConfigurationEncoding.tape_length_le store
      simp only [control, controlFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, rewinding, FiniteBitEncoding.prod_encode_length,
        native, tape, pc, SourceStorage.controlCells]
      omega
  | finished result => simp [control, controlFields, FiniteBitEncoding.sum,
      Machine.ConfigurationEncoding.bit, pc, SourceStorage.controlCells]

def trace := (bits.prod bits).list

theorem trace_length_le (history : List (List Bool × List Bool)) :
    (trace.encode history).length ≤ 4 * SourceStorage.traceCells history + 4 * history.length + 1 := by
  induction history with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨request, response⟩
      simp only [trace, FiniteBitEncoding.list_encode_cons_length,
        FiniteBitEncoding.prod_encode_length, bits, id_eq, SourceStorage.traceCells, List.length_cons]
      simp only [trace, bits] at ih
      omega

def frameFields {State : Type u} (E : FiniteBitEncoding State) := E.prod (control.prod trace)

def frame {State : Type u} (E : FiniteBitEncoding State) : FiniteBitEncoding (Configuration State) where
  encode := fun c => (frameFields E).encode (c.state, c.control, c.reverseTrace)
  decode := fun raw => ((frameFields E).decode raw).map fun fields => ⟨fields.1, fields.2.1, fields.2.2⟩
  decode_encode := by intro c; simp [(frameFields E).decode_encode]

theorem frame_length_le {State : Type u} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state) (c : Configuration State) :
    ((frame E).encode c).length ≤
      8 * pc c.control + 72 * SourceStorage.cells stateSize c + 4 * c.reverseTrace.length + 100 := by
  have hs := hState c.state
  have hc := control_length_le c.control
  have ht := trace_length_le c.reverseTrace
  simp only [frame, frameFields, FiniteBitEncoding.prod_encode_length]
  unfold SourceStorage.cells
  omega

theorem frame_extent_length_le {State : Type u} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state) (c : Configuration State) :
    ((frame E).encode c).length ≤ 8 * pc c.control +
      72 * (2 * (ControllerExtent.frameExtent stateSize c) ^ 2 + 5 * ControllerExtent.frameExtent stateSize c + 1) +
      4 * ControllerExtent.frameExtent stateSize c + 100 := by
  have hf := frame_length_le E stateSize hState c
  have hc := ControllerExtent.frame_cells stateSize c
  have ht := ControllerExtent.trace_length c.reverseTrace
  have he : ControllerExtent.traceExtent c.reverseTrace ≤ ControllerExtent.frameExtent stateSize c := by
    simp only [ControllerExtent.frameExtent]; omega
  have hl := ht.trans he
  omega

end CryptoOracle.Interactive.ConfigurationEncoding
