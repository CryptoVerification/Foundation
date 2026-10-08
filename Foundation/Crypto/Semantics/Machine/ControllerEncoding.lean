import Foundation.Crypto.Semantics.Machine.PreparationEncoding

/-! Faithful codecs for key initialization, response writing/export and
preparation failure recovery. Bounds include phase tags, retained temporary
lists and native program counters; codecs do not supply execution costs. -/
namespace Machine.ControllerEncoding
open Foundation.Probability
def tape := ConfigurationEncoding.tape
def bits := FiniteBitEncoding.bitstring

def optionalBits : FiniteBitEncoding (Option (List Bool)) where
  encode := fun value => match value with | none => [false] | some payload => true :: payload
  decode := fun raw => match raw with | [false] => some none | true :: payload => some (some payload) | _ => none
  decode_encode := by intro value; cases value <;> rfl

def packetFields := optionalBits.sum ((bits.prod tape).sum ((bits.prod tape).sum tape))
def packet : FiniteBitEncoding ResponsePacket.Control where
  encode := fun c => packetFields.encode (match c with
    | .start response => .inl response
    | .writing rest store => .inr (.inl (rest, store))
    | .advancing rest store => .inr (.inr (.inl (rest, store)))
    | .returned store => .inr (.inr (.inr store)))
  decode := fun raw => (packetFields.decode raw).map fun f => match f with
    | .inl response => .start response
    | .inr (.inl (rest, store)) => .writing rest store
    | .inr (.inr (.inl (rest, store))) => .advancing rest store
    | .inr (.inr (.inr store)) => .returned store
  decode_encode := by intro c; cases c <;> simp [packetFields.decode_encode]

theorem packet_length_le (c : ResponsePacket.Control) :
    (packet.encode c).length ≤ 6 * ControllerStorage.packetCells c + 8 := by
  cases c with
  | start response => cases response <;> simp [packet, packetFields, FiniteBitEncoding.sum, optionalBits, ControllerStorage.packetCells] <;> omega
  | writing rest store =>
      have ht := ConfigurationEncoding.tape_length_le store
      simp only [packet, packetFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.prod_encode_length,
        bits, FiniteBitEncoding.bitstring, id_eq, tape, ControllerStorage.packetCells]
      omega
  | advancing rest store =>
      have ht := ConfigurationEncoding.tape_length_le store
      simp only [packet, packetFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.prod_encode_length,
        bits, FiniteBitEncoding.bitstring, id_eq, tape, ControllerStorage.packetCells]
      omega
  | returned store =>
      have ht := ConfigurationEncoding.tape_length_le store
      simp only [packet, packetFields, FiniteBitEncoding.sum_encode_inr_length, tape, ControllerStorage.packetCells]
      omega

def exportFields := ConfigurationEncoding.configuration.sum
  (tape.sum ((tape.prod bits).sum ((bits.prod bits).sum bits)))
def responseExport : FiniteBitEncoding ResponseExport.Control where
  encode := fun c => exportFields.encode (match c with
    | .running machine => .inl machine
    | .rewinding store => .inr (.inl store)
    | .collecting store acc => .inr (.inr (.inl (store, acc)))
    | .reversing rest payload => .inr (.inr (.inr (.inl (rest, payload))))
    | .returned payload => .inr (.inr (.inr (.inr payload))))
  decode := fun raw => (exportFields.decode raw).map fun f => match f with
    | .inl machine => .running machine
    | .inr (.inl store) => .rewinding store
    | .inr (.inr (.inl (store, acc))) => .collecting store acc
    | .inr (.inr (.inr (.inl (rest, payload)))) => .reversing rest payload
    | .inr (.inr (.inr (.inr payload))) => .returned payload
  decode_encode := by intro c; cases c <;> simp [exportFields.decode_encode]

def exportPc : ResponseExport.Control → Nat
  | .running machine => machine.pc
  | _ => 0

theorem export_length_le (c : ResponseExport.Control) :
    (responseExport.encode c).length ≤ 2 * exportPc c + 18 * ControllerStorage.exportCells c + 20 := by
  cases c with
  | running machine =>
      have hm := ConfigurationEncoding.configuration_length_le machine
      simp only [responseExport, exportFields, FiniteBitEncoding.sum_encode_inl_length, exportPc, ControllerStorage.exportCells]
      omega
  | rewinding store =>
      have ht := ConfigurationEncoding.tape_length_le store
      simp only [responseExport, exportFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, tape, exportPc, ControllerStorage.exportCells]
      omega
  | collecting store acc =>
      have ht := ConfigurationEncoding.tape_length_le store
      simp only [responseExport, exportFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.prod_encode_length,
        tape, bits, FiniteBitEncoding.bitstring, id_eq, exportPc, ControllerStorage.exportCells]
      omega
  | reversing rest payload =>
      simp [responseExport, exportFields, FiniteBitEncoding.sum, FiniteBitEncoding.prod_encode_length,
        bits, FiniteBitEncoding.bitstring, id_eq, exportPc, ControllerStorage.exportCells]
      omega
  | returned payload =>
      simp [responseExport, exportFields, FiniteBitEncoding.sum, bits, FiniteBitEncoding.bitstring, id_eq, exportPc, ControllerStorage.exportCells]
      omega

def initializationFields := ConfigurationEncoding.configuration.sum (tape.sum tape)
def initialization : FiniteBitEncoding PrivateInitialization.Control where
  encode := fun c => initializationFields.encode (match c with
    | .generating machine => .inl machine | .rewinding store => .inr (.inl store) | .ready store => .inr (.inr store))
  decode := fun raw => (initializationFields.decode raw).map fun f => match f with
    | .inl machine => .generating machine | .inr (.inl store) => .rewinding store | .inr (.inr store) => .ready store
  decode_encode := by intro c; cases c <;> simp [initializationFields.decode_encode]

def initializationPc : PrivateInitialization.Control → Nat
  | .generating machine => machine.pc
  | _ => 0

theorem initialization_length_le (c : PrivateInitialization.Control) :
    (initialization.encode c).length ≤ 2 * initializationPc c + 18 * ControllerStorage.initializationCells c + 20 := by
  cases c with
  | generating machine =>
      have hm := ConfigurationEncoding.configuration_length_le machine
      simp only [initialization, initializationFields, FiniteBitEncoding.sum_encode_inl_length,
        initializationPc, ControllerStorage.initializationCells]
      omega
  | rewinding store =>
      have ht := ConfigurationEncoding.tape_length_le store
      simp only [initialization, initializationFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, tape, initializationPc, ControllerStorage.initializationCells]
      omega
  | ready store =>
      have ht := ConfigurationEncoding.tape_length_le store
      simp only [initialization, initializationFields, FiniteBitEncoding.sum_encode_inr_length,
        tape, initializationPc, ControllerStorage.initializationCells]
      omega

def tripleTape := tape.prod (tape.prod tape)
private theorem triple_length_le (a b c : Tape) :
    (tripleTape.encode (a, b, c)).length ≤ 12 * (a.cells + b.cells + c.cells) + 17 := by
  have ha := ConfigurationEncoding.tape_length_le a
  have hb := ConfigurationEncoding.tape_length_le b
  have hc := ConfigurationEncoding.tape_length_le c
  simp only [tripleTape, FiniteBitEncoding.prod_encode_length, tape]
  omega

def failureFields := tripleTape.sum (PreparationEncoding.pair.sum
  ((tape.prod (tape.prod packet)).sum tripleTape))
def failure : FiniteBitEncoding PreparationFailure.Control where
  encode := fun c => failureFields.encode (match c with
    | .detected a b c => .inl (a, b, c)
    | .restoring preparation => .inr (.inl preparation)
    | .writing a b response => .inr (.inr (.inl (a, b, response)))
    | .returned a b c => .inr (.inr (.inr (a, b, c))))
  decode := fun raw => (failureFields.decode raw).map fun f => match f with
    | .inl (a, b, c) => .detected a b c
    | .inr (.inl preparation) => .restoring preparation
    | .inr (.inr (.inl (a, b, response))) => .writing a b response
    | .inr (.inr (.inr (a, b, c))) => .returned a b c
  decode_encode := by intro c; cases c <;> simp [failureFields.decode_encode]

theorem failure_length_le (c : PreparationFailure.Control) :
    (failure.encode c).length ≤ 24 * ControllerStorage.failureCells c + 100 := by
  cases c with
  | detected a b c =>
      have ht := triple_length_le a b c
      simp only [failure, failureFields, FiniteBitEncoding.sum_encode_inl_length, ControllerStorage.failureCells]
      omega
  | restoring preparation =>
      have hp := PreparationEncoding.pair_length_le preparation
      simp only [failure, failureFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, ControllerStorage.failureCells]
      omega
  | writing a b response =>
      have ha := ConfigurationEncoding.tape_length_le a
      have hb := ConfigurationEncoding.tape_length_le b
      have hp := packet_length_le response
      simp only [failure, failureFields, FiniteBitEncoding.sum_encode_inr_length,
        FiniteBitEncoding.sum_encode_inl_length, FiniteBitEncoding.prod_encode_length,
        tape, ControllerStorage.failureCells]
      omega
  | returned a b c =>
      have ht := triple_length_le a b c
      simp only [failure, failureFields, FiniteBitEncoding.sum_encode_inr_length, ControllerStorage.failureCells]
      omega

def checkFields := PreparationEncoding.pair.sum failure
def check : FiniteBitEncoding PreparationCheck.Control where
  encode := fun c => checkFields.encode (match c with | .preparing p => .inl p | .failure r => .inr r)
  decode := fun raw => (checkFields.decode raw).map fun f => match f with | .inl p => .preparing p | .inr r => .failure r
  decode_encode := by intro c; cases c <;> simp [checkFields.decode_encode]

theorem check_length_le (c : PreparationCheck.Control) :
    (check.encode c).length ≤ 24 * ControllerStorage.checkCells c + 101 := by
  cases c with
  | preparing p =>
      have hp := PreparationEncoding.pair_length_le p
      simp only [check, checkFields, FiniteBitEncoding.sum_encode_inl_length, ControllerStorage.checkCells]
      omega
  | failure r =>
      have hr := failure_length_le r
      simp only [check, checkFields, FiniteBitEncoding.sum_encode_inr_length, ControllerStorage.checkCells]
      omega

end Machine.ControllerEncoding
