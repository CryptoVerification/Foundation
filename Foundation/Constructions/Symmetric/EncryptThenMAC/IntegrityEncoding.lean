import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityStorage
import Foundation.Crypto.Semantics.Machine.ControllerEncoding
import Foundation.Crypto.Semantics.Oracle.ConfigurationEncoding

/-! Complete integrity-controller representation, retaining phase counters as
well as addresses, private bits, temporary copies and both histories. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityEncoding
open Machine CryptoOracle.Interactive
universe u
abbrev tape := Machine.ConfigurationEncoding.tape
abbrev bits := FiniteBitEncoding.bitstring
abbrev native := Machine.ConfigurationEncoding.configuration
abbrev bit := Machine.ConfigurationEncoding.bit
abbrev number := Machine.ConfigurationEncoding.unary
abbrev source := CryptoOracle.Interactive.ConfigurationEncoding.control

def preparationFields := (number.prod tape).sum native
def preparation : FiniteBitEncoding IntegrityPreparation.Control :=
  preparationFields.retract
    (fun c => match c with | .preparing phase t => .inl (phase, t) | .encrypting c => .inr c)
    (fun f => match f with | .inl (phase, t) => .preparing phase t | .inr c => .encrypting c)
    (by intro c; cases c <;> rfl)

def preparationScalar : IntegrityPreparation.Control → Nat
  | .preparing phase _ => phase | .encrypting c => c.pc

theorem preparation_length (c : IntegrityPreparation.Control) :
    (preparation.encode c).length ≤ 2 * preparationScalar c + 18 * IntegrityStorage.preparationCells c + 16 := by
  cases c with
  | preparing phase t =>
      have ht := Machine.ConfigurationEncoding.tape_length_le t
      simp only [preparation, FiniteBitEncoding.retract_encode_length, preparationFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.prod_encode_length,
        number, Machine.ConfigurationEncoding.unary, List.length_replicate,
        tape, preparationScalar, IntegrityStorage.preparationCells]
      omega
  | encrypting c =>
      have hc := Machine.ConfigurationEncoding.configuration_length_le c
      simp only [preparation, FiniteBitEncoding.retract_encode_length, preparationFields,
        FiniteBitEncoding.sum_encode_inr_length, native, preparationScalar, IntegrityStorage.preparationCells]
      omega

def controlFields := (source.prod (native)).sum ((bit.prod (bit.prod (source))).sum ((bit.prod (bit.prod (native.prod (bits.prod (preparation))))).sum ((bit.prod (native.prod (bits))).sum ((bit.prod (native.prod (bits.prod (bit.prod (bits.prod (number.prod (tape))))))).sum ((bit.prod (native.prod (bits.prod (bits.prod (tape))))).sum ((bit.prod (native.prod (bits.prod (bits.prod (tape))))).sum ((bit.prod (native.prod (bits.prod (tape)))).sum ((bit.prod (native.prod (bits.prod (tape.prod (bits))))).sum (bit.prod (native.prod (bits.prod (bits.prod (bits)))))))))))))

abbrev ControlData := (IntegrityMachine.SourceControl × Configuration) ⊕ ((Bool × Bool × IntegrityMachine.SourceControl) ⊕ ((Bool × Bool × Configuration × List Bool × IntegrityPreparation.Control) ⊕ ((Bool × Configuration × List Bool) ⊕ ((Bool × Configuration × List Bool × Bool × List Bool × Nat × Tape) ⊕ ((Bool × Configuration × List Bool × List Bool × Tape) ⊕ ((Bool × Configuration × List Bool × List Bool × Tape) ⊕ ((Bool × Configuration × List Bool × Tape) ⊕ ((Bool × Configuration × List Bool × Tape × List Bool) ⊕ ((Bool × Configuration × List Bool × List Bool × List Bool))))))))))

def controlPack : IntegrityMachine.Control → ControlData
  | .initializing s g => .inl (s, g)
  | .source key used s => .inr (.inl (key, used, s))
  | .encrypting key used c request p => .inr (.inr (.inl (key, used, c, request, p)))
  | .failure key c request => .inr (.inr (.inr (.inl (key, c, request))))
  | .header key c request ciphertext tag phase t => .inr (.inr (.inr (.inr (.inl (key, c, request, ciphertext, tag, phase, t)))))
  | .copying key c request rest t => .inr (.inr (.inr (.inr (.inr (.inl (key, c, request, rest, t))))))
  | .advancing key c request rest t => .inr (.inr (.inr (.inr (.inr (.inr (.inl (key, c, request, rest, t)))))))
  | .rewinding key c request t => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (key, c, request, t))))))))
  | .collecting key c request t acc => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (key, c, request, t, acc)))))))))
  | .reversing key c request rest response => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ((key, c, request, rest, response))))))))))

def controlUnpack : ControlData → IntegrityMachine.Control
  | .inl (s, g) => .initializing s g
  | .inr (.inl (key, used, s)) => .source key used s
  | .inr (.inr (.inl (key, used, c, request, p))) => .encrypting key used c request p
  | .inr (.inr (.inr (.inl (key, c, request)))) => .failure key c request
  | .inr (.inr (.inr (.inr (.inl (key, c, request, ciphertext, tag, phase, t))))) => .header key c request ciphertext tag phase t
  | .inr (.inr (.inr (.inr (.inr (.inl (key, c, request, rest, t)))))) => .copying key c request rest t
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (key, c, request, rest, t))))))) => .advancing key c request rest t
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (key, c, request, t)))))))) => .rewinding key c request t
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (key, c, request, t, acc))))))))) => .collecting key c request t acc
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ((key, c, request, rest, response)))))))))) => .reversing key c request rest response

def control : FiniteBitEncoding IntegrityMachine.Control :=
  controlFields.retract controlPack controlUnpack (by intro c; cases c <;> rfl)

def scalar : IntegrityMachine.Control → Nat
  | .initializing s g => CryptoOracle.Interactive.ConfigurationEncoding.pc s + g.pc
  | .source _ _ s => CryptoOracle.Interactive.ConfigurationEncoding.pc s
  | .encrypting _ _ c _ p => c.pc + preparationScalar p
  | .header _ c _ _ _ phase _ => c.pc + phase
  | .failure _ c _ | .copying _ c _ _ _ | .advancing _ c _ _ _ |
      .rewinding _ c _ _ | .collecting _ c _ _ _ | .reversing _ c _ _ _ => c.pc

theorem control_length (c : IntegrityMachine.Control) :
    (control.encode c).length ≤ 8 * scalar c + 72 * IntegrityStorage.controlCells c + 256 := by
  cases c with
  | initializing s g =>
      have h_s := CryptoOracle.Interactive.ConfigurationEncoding.control_length_le s
      have h_g := Machine.ConfigurationEncoding.configuration_length_le g
      simp only [control, FiniteBitEncoding.retract_encode_length, controlPack, controlFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, bits, FiniteBitEncoding.bitstring, id_eq,
        bit, Machine.ConfigurationEncoding.bit, List.length_singleton,
        number, Machine.ConfigurationEncoding.unary, List.length_replicate,
        tape, native, source, scalar, IntegrityStorage.controlCells]
      omega
  | source key used s =>
      have h_s := CryptoOracle.Interactive.ConfigurationEncoding.control_length_le s
      simp only [control, FiniteBitEncoding.retract_encode_length, controlPack, controlFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, bits, FiniteBitEncoding.bitstring, id_eq,
        bit, Machine.ConfigurationEncoding.bit, List.length_singleton,
        number, Machine.ConfigurationEncoding.unary, List.length_replicate,
        tape, native, source, scalar, IntegrityStorage.controlCells]
      omega
  | encrypting key used c request p =>
      have h_c := Machine.ConfigurationEncoding.configuration_length_le c
      have h_p := preparation_length p
      simp only [control, FiniteBitEncoding.retract_encode_length, controlPack, controlFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, bits, FiniteBitEncoding.bitstring, id_eq,
        bit, Machine.ConfigurationEncoding.bit, List.length_singleton,
        number, Machine.ConfigurationEncoding.unary, List.length_replicate,
        tape, native, source, scalar, IntegrityStorage.controlCells]
      omega
  | failure key c request =>
      have h_c := Machine.ConfigurationEncoding.configuration_length_le c
      simp only [control, FiniteBitEncoding.retract_encode_length, controlPack, controlFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, bits, FiniteBitEncoding.bitstring, id_eq,
        bit, Machine.ConfigurationEncoding.bit, List.length_singleton,
        number, Machine.ConfigurationEncoding.unary, List.length_replicate,
        tape, native, source, scalar, IntegrityStorage.controlCells]
      omega
  | header key c request ciphertext tag phase t =>
      have h_c := Machine.ConfigurationEncoding.configuration_length_le c
      have h_t := Machine.ConfigurationEncoding.tape_length_le t
      simp only [control, FiniteBitEncoding.retract_encode_length, controlPack, controlFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, bits, FiniteBitEncoding.bitstring, id_eq,
        bit, Machine.ConfigurationEncoding.bit, List.length_singleton,
        number, Machine.ConfigurationEncoding.unary, List.length_replicate,
        tape, native, source, scalar, IntegrityStorage.controlCells]
      omega
  | copying key c request rest t =>
      have h_c := Machine.ConfigurationEncoding.configuration_length_le c
      have h_t := Machine.ConfigurationEncoding.tape_length_le t
      simp only [control, FiniteBitEncoding.retract_encode_length, controlPack, controlFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, bits, FiniteBitEncoding.bitstring, id_eq,
        bit, Machine.ConfigurationEncoding.bit, List.length_singleton,
        number, Machine.ConfigurationEncoding.unary, List.length_replicate,
        tape, native, source, scalar, IntegrityStorage.controlCells]
      omega
  | advancing key c request rest t =>
      have h_c := Machine.ConfigurationEncoding.configuration_length_le c
      have h_t := Machine.ConfigurationEncoding.tape_length_le t
      simp only [control, FiniteBitEncoding.retract_encode_length, controlPack, controlFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, bits, FiniteBitEncoding.bitstring, id_eq,
        bit, Machine.ConfigurationEncoding.bit, List.length_singleton,
        number, Machine.ConfigurationEncoding.unary, List.length_replicate,
        tape, native, source, scalar, IntegrityStorage.controlCells]
      omega
  | rewinding key c request t =>
      have h_c := Machine.ConfigurationEncoding.configuration_length_le c
      have h_t := Machine.ConfigurationEncoding.tape_length_le t
      simp only [control, FiniteBitEncoding.retract_encode_length, controlPack, controlFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, bits, FiniteBitEncoding.bitstring, id_eq,
        bit, Machine.ConfigurationEncoding.bit, List.length_singleton,
        number, Machine.ConfigurationEncoding.unary, List.length_replicate,
        tape, native, source, scalar, IntegrityStorage.controlCells]
      omega
  | collecting key c request t acc =>
      have h_c := Machine.ConfigurationEncoding.configuration_length_le c
      have h_t := Machine.ConfigurationEncoding.tape_length_le t
      simp only [control, FiniteBitEncoding.retract_encode_length, controlPack, controlFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, bits, FiniteBitEncoding.bitstring, id_eq,
        bit, Machine.ConfigurationEncoding.bit, List.length_singleton,
        number, Machine.ConfigurationEncoding.unary, List.length_replicate,
        tape, native, source, scalar, IntegrityStorage.controlCells]
      omega
  | reversing key c request rest response =>
      have h_c := Machine.ConfigurationEncoding.configuration_length_le c
      simp only [control, FiniteBitEncoding.retract_encode_length, controlPack, controlFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, bits, FiniteBitEncoding.bitstring, id_eq,
        bit, Machine.ConfigurationEncoding.bit, List.length_singleton,
        number, Machine.ConfigurationEncoding.unary, List.length_replicate,
        tape, native, source, scalar, IntegrityStorage.controlCells]
      omega

def signingTrace := (bit.prod bits).list

theorem signing_length (history : List (Bool × List Bool)) :
    (signingTrace.encode history).length ≤
      4 * SourceStorage.traceCells (IntegrityStorage.signingTrace history) + 4 * history.length + 1 := by
  induction history with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨b, tag⟩
      simp only [signingTrace, FiniteBitEncoding.list_encode_cons_length,
        FiniteBitEncoding.prod_encode_length, bit, Machine.ConfigurationEncoding.bit,
        bits, FiniteBitEncoding.bitstring, id_eq, List.length_singleton,
        IntegrityStorage.signingTrace, List.map_cons, SourceStorage.traceCells, List.length_cons] at *
      omega

def frameFields {State : Type u} (E : FiniteBitEncoding State) :=
  E.prod (control.prod (CryptoOracle.Interactive.ConfigurationEncoding.trace.prod signingTrace))
def frame {State : Type u} (E : FiniteBitEncoding State) : FiniteBitEncoding (IntegrityMachine.Frame State) :=
  (frameFields E).retract (fun f => (f.state, f.control, f.sourceTrace, f.signingTrace))
    (fun (s, c, t, e) => ⟨s, c, t, e⟩) (by intro f; rfl)

theorem frame_length {State : Type u} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state) (f : IntegrityMachine.Frame State) :
    ((frame E).encode f).length ≤ 16 * scalar f.control + 144 * IntegrityStorage.cells stateSize f +
      8 * (f.sourceTrace.length + f.signingTrace.length) + 522 := by
  have hs := hState f.state
  have hc := control_length f.control
  have ht := CryptoOracle.Interactive.ConfigurationEncoding.trace_length_le f.sourceTrace
  have he := signing_length f.signingTrace
  simp only [frame, FiniteBitEncoding.retract_encode_length, frameFields, FiniteBitEncoding.prod_encode_length]
  unfold IntegrityStorage.cells
  omega

end Foundation.Symmetric.EncryptThenMAC.IntegrityEncoding
