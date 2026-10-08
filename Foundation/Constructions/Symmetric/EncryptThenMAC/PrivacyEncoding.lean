import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyStorage
import Foundation.Crypto.Semantics.Machine.ControllerEncoding
import Foundation.Crypto.Semantics.Oracle.ConfigurationEncoding

/-! Faithful bit representation of the second construction's entire privacy
controller, including both histories and simultaneous private/caller frames.
Static bounds include address fields; operational address bounds are separate. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyEncoding
open Machine CryptoOracle.Interactive
universe u
abbrev tape := Machine.ConfigurationEncoding.tape
abbrev bits := FiniteBitEncoding.bitstring
abbrev native := Machine.ConfigurationEncoding.configuration

def generatorPack : PrivateKeyGeneration.Control → PrivateInitialization.Control
  | .generating c => .generating c | .rewinding t => .rewinding t | .ready t => .ready t

def generatorUnpack : PrivateInitialization.Control → PrivateKeyGeneration.Control
  | .generating c => .generating c | .rewinding t => .rewinding t | .ready t => .ready t

def generator : FiniteBitEncoding PrivateKeyGeneration.Control :=
  ControllerEncoding.initialization.retract generatorPack generatorUnpack (by intro c; cases c <;> rfl)

def generatorPc : PrivateKeyGeneration.Control → Nat
  | .generating c => c.pc | _ => 0

theorem generator_length (c : PrivateKeyGeneration.Control) :
    (generator.encode c).length ≤ 2 * generatorPc c + 18 * PrivacyStorage.generatorCells c + 20 := by
  have h := ControllerEncoding.initialization_length_le (generatorPack c)
  cases c <;> exact h

def responderFields := (tape.prod (bits.prod tape)).sum
  ((tape.prod (bits.prod tape)).sum (native.sum ((tape.prod tape).sum (tape.prod native))))
abbrev ResponderData := (Tape × List Bool × Tape) ⊕
  ((Tape × List Bool × Tape) ⊕ (Configuration ⊕ ((Tape × Tape) ⊕ (Tape × Configuration))))
def responderPack : ResponseHandoff.Control → ResponderData
  | .headerWriting key rest buffer => .inl (key, rest, buffer)
  | .headerAdvancing key rest buffer => .inr (.inl (key, rest, buffer))
  | .copying c => .inr (.inr (.inl c))
  | .rewinding key buffer => .inr (.inr (.inr (.inl (key, buffer))))
  | .authenticating key c => .inr (.inr (.inr (.inr (key, c))))
def responderUnpack : ResponderData → ResponseHandoff.Control
  | .inl (key, rest, buffer) => .headerWriting key rest buffer
  | .inr (.inl (key, rest, buffer)) => .headerAdvancing key rest buffer
  | .inr (.inr (.inl c)) => .copying c
  | .inr (.inr (.inr (.inl (key, buffer)))) => .rewinding key buffer
  | .inr (.inr (.inr (.inr (key, c)))) => .authenticating key c

def responder : FiniteBitEncoding ResponseHandoff.Control :=
  responderFields.retract responderPack responderUnpack (by intro c; cases c <;> rfl)

def responderPc : ResponseHandoff.Control → Nat
  | .copying c | .authenticating _ c => c.pc | _ => 0

theorem responder_length (c : ResponseHandoff.Control) :
    (responder.encode c).length ≤ 2 * responderPc c + 18 * PrivacyStorage.responderCells c + 32 := by
  cases c with
  | headerWriting key rest buffer | headerAdvancing key rest buffer =>
      have hk := Machine.ConfigurationEncoding.tape_length_le key
      have hb := Machine.ConfigurationEncoding.tape_length_le buffer
      simp only [responder, FiniteBitEncoding.retract_encode_length, responderPack, responderFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, bits, FiniteBitEncoding.bitstring, id_eq,
        tape, native, responderPc, PrivacyStorage.responderCells]
      omega
  | copying c =>
      have hc := Machine.ConfigurationEncoding.configuration_length_le c
      simp only [responder, FiniteBitEncoding.retract_encode_length, responderPack, responderFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        tape, native, responderPc, PrivacyStorage.responderCells]
      omega
  | rewinding key buffer =>
      have hk := Machine.ConfigurationEncoding.tape_length_le key
      have hb := Machine.ConfigurationEncoding.tape_length_le buffer
      simp only [responder, FiniteBitEncoding.retract_encode_length, responderPack, responderFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, tape, native, responderPc, PrivacyStorage.responderCells]
      omega
  | authenticating key c =>
      have hk := Machine.ConfigurationEncoding.tape_length_le key
      have hc := Machine.ConfigurationEncoding.configuration_length_le c
      simp only [responder, FiniteBitEncoding.retract_encode_length, responderPack, responderFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, tape, native, responderPc, PrivacyStorage.responderCells]
      omega

abbrev source := CryptoOracle.Interactive.ConfigurationEncoding.control

def controlFields := (source.prod generator).sum ((tape.prod source).sum
  ((native.prod (bits.prod responder)).sum ((tape.prod (native.prod (bits.prod tape))).sum
    ((tape.prod (native.prod (bits.prod (tape.prod bits)))).sum
      (tape.prod (native.prod (bits.prod (bits.prod bits))))))))

abbrev ControlData := (PrivacyMachine.Source.Control × PrivateKeyGeneration.Control) ⊕
  ((Tape × PrivacyMachine.Source.Control) ⊕ ((Configuration × List Bool × ResponseHandoff.Control) ⊕
    ((Tape × Configuration × List Bool × Tape) ⊕
      ((Tape × Configuration × List Bool × Tape × List Bool) ⊕
        (Tape × Configuration × List Bool × List Bool × List Bool)))))
def controlPack : PrivacyMachine.Control → ControlData
  | .initializing s g => .inl (s, g)
  | .source key s => .inr (.inl (key, s))
  | .responding c request r => .inr (.inr (.inl (c, request, r)))
  | .rewinding key c request t => .inr (.inr (.inr (.inl (key, c, request, t))))
  | .collecting key c request t acc => .inr (.inr (.inr (.inr (.inl (key, c, request, t, acc)))))
  | .reversing key c request rest response => .inr (.inr (.inr (.inr (.inr (key, c, request, rest, response)))))
def controlUnpack : ControlData → PrivacyMachine.Control
  | .inl (s, g) => .initializing s g
  | .inr (.inl (key, s)) => .source key s
  | .inr (.inr (.inl (c, request, r))) => .responding c request r
  | .inr (.inr (.inr (.inl (key, c, request, t)))) => .rewinding key c request t
  | .inr (.inr (.inr (.inr (.inl (key, c, request, t, acc))))) => .collecting key c request t acc
  | .inr (.inr (.inr (.inr (.inr (key, c, request, rest, response))))) => .reversing key c request rest response

def control : FiniteBitEncoding PrivacyMachine.Control :=
  controlFields.retract controlPack controlUnpack (by intro c; cases c <;> rfl)

def pc : PrivacyMachine.Control → Nat
  | .initializing s g => CryptoOracle.Interactive.ConfigurationEncoding.pc s + generatorPc g
  | .source _ s => CryptoOracle.Interactive.ConfigurationEncoding.pc s
  | .responding c _ r => c.pc + responderPc r
  | .rewinding _ c _ _ | .collecting _ c _ _ _ | .reversing _ c _ _ _ => c.pc

theorem control_length (c : PrivacyMachine.Control) :
    (control.encode c).length ≤ 8 * pc c + 72 * PrivacyStorage.controlCells c + 160 := by
  cases c with
  | initializing s g =>
      have hs := CryptoOracle.Interactive.ConfigurationEncoding.control_length_le s
      have hg := generator_length g
      simp only [control, FiniteBitEncoding.retract_encode_length, controlPack, controlFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.prod_encode_length,
        tape, native, source, pc, PrivacyStorage.controlCells]
      omega
  | source key s =>
      have hk := Machine.ConfigurationEncoding.tape_length_le key
      have hs := CryptoOracle.Interactive.ConfigurationEncoding.control_length_le s
      simp only [control, FiniteBitEncoding.retract_encode_length, controlPack, controlFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, tape, native, source, pc, PrivacyStorage.controlCells]
      omega
  | responding c request r =>
      have hc := Machine.ConfigurationEncoding.configuration_length_le c
      have hr := responder_length r
      simp only [control, FiniteBitEncoding.retract_encode_length, controlPack, controlFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, bits, FiniteBitEncoding.bitstring, id_eq,
        tape, native, source, pc, PrivacyStorage.controlCells]
      omega
  | rewinding key c request t =>
      have hk := Machine.ConfigurationEncoding.tape_length_le key
      have hc := Machine.ConfigurationEncoding.configuration_length_le c
      have ht := Machine.ConfigurationEncoding.tape_length_le t
      simp only [control, FiniteBitEncoding.retract_encode_length, controlPack, controlFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, bits, FiniteBitEncoding.bitstring, id_eq,
        tape, native, source, pc, PrivacyStorage.controlCells]
      omega
  | collecting key c request t acc =>
      have hk := Machine.ConfigurationEncoding.tape_length_le key
      have hc := Machine.ConfigurationEncoding.configuration_length_le c
      have ht := Machine.ConfigurationEncoding.tape_length_le t
      simp only [control, FiniteBitEncoding.retract_encode_length, controlPack, controlFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, bits, FiniteBitEncoding.bitstring, id_eq,
        tape, native, source, pc, PrivacyStorage.controlCells]
      omega
  | reversing key c request rest response =>
      have hk := Machine.ConfigurationEncoding.tape_length_le key
      have hc := Machine.ConfigurationEncoding.configuration_length_le c
      simp only [control, FiniteBitEncoding.retract_encode_length, controlPack, controlFields,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.prod_encode_length, bits, FiniteBitEncoding.bitstring, id_eq,
        tape, native, source, pc, PrivacyStorage.controlCells]
      omega

def frameFields {State : Type u} (E : FiniteBitEncoding State) :=
  E.prod (control.prod (CryptoOracle.Interactive.ConfigurationEncoding.trace.prod
    CryptoOracle.Interactive.ConfigurationEncoding.trace))
def frame {State : Type u} (E : FiniteBitEncoding State) : FiniteBitEncoding (PrivacyMachine.Frame State) :=
  (frameFields E).retract (fun f => (f.state, f.control, f.sourceTrace, f.externalTrace))
    (fun (s, c, t, e) => ⟨s, c, t, e⟩) (by intro f; rfl)

theorem frame_length {State : Type u} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state) (f : PrivacyMachine.Frame State) :
    ((frame E).encode f).length ≤ 16 * pc f.control + 144 * PrivacyStorage.cells stateSize f +
      8 * (f.sourceTrace.length + f.externalTrace.length) + 330 := by
  have hs := hState f.state
  have hc := control_length f.control
  have ht := CryptoOracle.Interactive.ConfigurationEncoding.trace_length_le f.sourceTrace
  have he := CryptoOracle.Interactive.ConfigurationEncoding.trace_length_le f.externalTrace
  simp only [frame, FiniteBitEncoding.retract_encode_length, frameFields, FiniteBitEncoding.prod_encode_length]
  unfold PrivacyStorage.cells
  omega

end Foundation.Symmetric.EncryptThenMAC.PrivacyEncoding
