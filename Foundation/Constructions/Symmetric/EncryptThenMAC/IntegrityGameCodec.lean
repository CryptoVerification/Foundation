import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegritySourceObservation
import Foundation.Constructions.Symmetric.EncryptThenMAC.AuthenticateResponse
import Foundation.Constructions.Symmetric.EncryptThenMAC.Integrity
import Foundation.Crypto.Semantics.Oracle.QueryDecode
import Foundation.Crypto.Semantics.Oracle.StateMap

/-! Typed integrity interface for the native source machine. Decoding is an
experiment observation, not a unit-cost native operation. All ciphertext/tag
responses, including failures, and the full transcript are preserved. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityGameCodec
open Machine Foundation.Probability CryptoOracle
set_option backward.isDefEq.respectTransparency false

def request (bytes : List Bool) : Bool := bytes.headD false

def decodeTag (width : Nat) (bytes : List Bool) : Bits width :=
  fun i => bytes[i.val]?.getD false

theorem tag_roundtrip {width : Nat} (tag : Bits width) : decodeTag width tag.toList = tag := by
  funext i
  simp [decodeTag, Bits.toList]

def decodeResponse (width : Nat) : List Bool → Option (Bool × Bits width)
  | true :: ciphertext :: tag => some (ciphertext, decodeTag width tag)
  | _ => none

theorem response_roundtrip {width : Nat} (value : Option (Bool × Bits width)) :
    decodeResponse width (AuthenticateResponse.encode value) = value := by
  cases value with
  | none => rfl
  | some value =>
      rcases value with ⟨ciphertext, tag⟩
      simp [AuthenticateResponse.encode, decodeResponse, tag_roundtrip]

/-- Final forgery packets use one ciphertext bit followed by the tag. Missing
cells are explicitly false; trailing cells beyond the public width are ignored. -/
def candidate (width : Nat) (control : Interactive.Control) : Bool × Bits width :=
  let bytes := (Interactive.Reification.packet control).getD []
  (bytes.headD false, decodeTag width bytes.tail)

def byteAttack (width : Nat) (code : Interactive.Code) (count : Nat) (input : List Bool) :
    Program (List Bool) (List Bool) (Bool × Bits width) :=
  (Interactive.Reification.program code count (.running (Configuration.initial input))).mapResult (candidate width)

def attack (width : Nat → Nat) (n : Nat) (code : Interactive.Code) (count : Nat) (input : List Bool) :
    IntegrityAttack OneBitEncryption.scheme (TableMAC.scheme width) n :=
  (byteAttack (width n) code count input).mapQueries request AuthenticateResponse.encode

theorem attack_queries (width : Nat → Nat) (n : Nat) (code : Interactive.Code) (count : Nat) (input : List Bool) :
    (attack width n code count input).BoundedQueries count :=
  Program.mapQueries_queries request AuthenticateResponse.encode
    (Program.mapResult_queries (candidate (width n)) (Interactive.Reification.program_queries code count _))

noncomputable def byteSigningOracle {width : Nat} (macKey : TableMAC.Key width) :
    Unit → Bool → PMF (Unit × List Bool) :=
  fun _ ciphertext => PMF.pure ((), (TableMAC.sign macKey ciphertext).toList)

theorem signing_length {width : Nat} (macKey : TableMAC.Key width) :
    IntegrityMachine.TagLength (byteSigningOracle macKey) width := by
  intro state ciphertext answer h
  simp only [byteSigningOracle, PMF.mem_support_pure_iff] at h
  subst answer
  simp

noncomputable def byteIntegrityOracle (width : Nat → Nat) (n : Nat) (key : Bool)
    (macKey : TableMAC.Key (width n)) : Interactive.BitOracle Bool :=
  Program.adaptOracle request AuthenticateResponse.encode
    (integrityOracle OneBitEncryption.scheme (TableMAC.scheme width) n key macKey)

theorem history_projection (width : Nat → Nat) (n : Nat) (key : Bool)
    (macKey : TableMAC.Key (width n)) (state : IntegrityMachine.SourceState Unit) (bytes : List Bool) :
    ((IntegrityMachine.sourceOracle (byteSigningOracle macKey) key) state bytes).map
      (fun answer => (answer.1.2.1, answer.2)) = byteIntegrityOracle width n key macKey state.2.1 bytes := by
  cases hu : state.2.1 <;>
    simp [IntegrityMachine.sourceOracle, byteSigningOracle, byteIntegrityOracle,
      Program.adaptOracle, request, integrityOracle, OneBitEncryption.scheme,
      authenticate, TableMAC.scheme, AuthenticateResponse.encode, hu, PMF.pure_map]

/-- Preserve the complete joint output, exhaustion state and typed public
transcript, rather than only the returned forgery candidate. -/
theorem typed_attack_run (width : Nat → Nat) (n : Nat) (key : Bool)
    (macKey : TableMAC.Key (width n)) (used : Bool) (code : Interactive.Code) (count : Nat) (input : List Bool) :
    (attack width n code count input).run
      (integrityOracle OneBitEncryption.scheme (TableMAC.scheme width) n key macKey) used =
      ((byteAttack (width n) code count input).run (byteIntegrityOracle width n key macKey) used).map
        (Program.mapTranscript request (decodeResponse (width n))) :=
  Program.mapQueries_run_decoded request AuthenticateResponse.encode (decodeResponse (width n))
    response_roundtrip _ _ _

theorem source_attack_run (width : Nat → Nat) (n : Nat) (key : Bool)
    (macKey : TableMAC.Key (width n)) (used : Bool) (code : Interactive.Code) (count : Nat) (input : List Bool) :
    (attack width n code count input).run
      (integrityOracle OneBitEncryption.scheme (TableMAC.scheme width) n key macKey) used =
      (Interactive.Reification.eval code (IntegrityMachine.sourceOracle (byteSigningOracle macKey) key) count
        ⟨((), used, []), .running (Configuration.initial input), []⟩).map (fun frame =>
          ⟨candidate (width n) frame.control, frame.state.2.1,
            frame.reverseTrace.reverse.map (fun pair => (request pair.1, decodeResponse (width n) pair.2))⟩) := by
  rw [typed_attack_run]
  have h := Program.run_state_map (fun state : IntegrityMachine.SourceState Unit => state.2.1)
    (IntegrityMachine.sourceOracle (byteSigningOracle macKey) key) (byteIntegrityOracle width n key macKey)
    (history_projection width n key macKey) (byteAttack (width n) code count input) ((), used, [])
  rw [← h, byteAttack, Interactive.Reification.decoded_program_run, PMF.map_comp, PMF.map_comp]
  rfl

end Foundation.Symmetric.EncryptThenMAC.IntegrityGameCodec
