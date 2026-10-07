import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacySourceObservation
import Foundation.Constructions.Symmetric.EncryptThenMAC.Security
import Foundation.Crypto.Semantics.Oracle.StateMap

/-! Concrete typed chosen-plaintext interface for the one-bit encryption
and table MAC. Requests use their first two cells with explicit defaults;
output guesses read the current output cell, as in the native bit machine. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyGameCodec
open Machine Foundation.Probability CryptoOracle
set_option backward.isDefEq.respectTransparency false

def request (bytes : List Bool) : Bool × Bool :=
  (bytes[0]?.getD false, bytes[1]?.getD false)

def encodeRequest (value : Bool × Bool) : List Bool := [value.1, value.2]

def ciphertext : Option Bool → List Bool
  | none => [false]
  | some bit => [true, bit]

theorem request_roundtrip (value : Bool × Bool) : request (encodeRequest value) = value := by
  cases value
  rfl

theorem ciphertext_roundtrip (value : Option Bool) :
    PrivacyMachine.decodeCiphertext (ciphertext value) = value := by cases value <;> rfl

def guess : CryptoOracle.Interactive.Control → Bool
  | .running machine => machine.outputTape.current.getD false
  | .finished bit => bit
  | _ => false

def nativeGuess (frame : PrivacyMachine.Frame State) : Bool :=
  match frame.control with
  | .source _ control => guess control
  | _ => false

def viewGuess (value : Option (CryptoOracle.Interactive.Configuration State)) : Bool :=
  match value with
  | some frame => guess frame.control
  | none => false

theorem viewGuess_sourceView (frame : PrivacyMachine.Frame State) :
    viewGuess (PrivacyMachine.sourceView frame) = nativeGuess frame := by
  cases hc : frame.control <;> simp [PrivacyMachine.sourceView, viewGuess, nativeGuess, hc]

def byteAttack (code : CryptoOracle.Interactive.Code) (count : Nat) (input : List Bool) :
    Program (List Bool) (List Bool) Bool :=
  (CryptoOracle.Interactive.Reification.program code count (.running (Configuration.initial input))).mapResult guess

def attack (width : Nat → Nat) (n : Nat) (code : CryptoOracle.Interactive.Code)
    (count : Nat) (input : List Bool) : PrivacyAttack OneBitEncryption.scheme (TableMAC.scheme width) n :=
  (byteAttack code count input).mapQueries request AuthenticateResponse.encode

theorem attack_queries (width : Nat → Nat) (n : Nat) (code : CryptoOracle.Interactive.Code)
    (count : Nat) (input : List Bool) : (attack width n code count input).BoundedQueries count :=
  Program.mapQueries_queries request AuthenticateResponse.encode
    (Program.mapResult_queries guess (CryptoOracle.Interactive.Reification.program_queries code count _))

noncomputable def byteEncryptionOracle (n : Nat) (key side : Bool) :
    CryptoOracle.Interactive.BitOracle Bool :=
  Program.adaptOracle request ciphertext (encryptionOracle OneBitEncryption.scheme n key side)

noncomputable def bytePrivacyOracle (width : Nat → Nat) (n : Nat) (key : Bool)
    (macKey : TableMAC.Key (width n)) (side : Bool) : CryptoOracle.Interactive.BitOracle Bool :=
  Program.adaptOracle request AuthenticateResponse.encode
    (privacyOracle OneBitEncryption.scheme (TableMAC.scheme width) n key macKey side)

/-- Erasing the observational raw history gives exactly the typed privacy
oracle's byte interface, including failed encryption responses. -/
theorem history_projection (width : Nat → Nat) (n : Nat) (key : Bool)
    (macKey : TableMAC.Key (width n)) (side : Bool)
    (state : Bool × List (List Bool × List Bool)) (bytes : List Bool) :
    ((PrivacyMachine.authenticatedOracle (byteEncryptionOracle n key side) macKey) state bytes).map
      (fun answer => (answer.1.1, answer.2)) = bytePrivacyOracle width n key macKey side state.1 bytes := by
  simp only [PrivacyMachine.authenticatedOracle, byteEncryptionOracle, bytePrivacyOracle,
    Program.adaptOracle, encryptionOracle, privacyOracle, PMF.pure_map,
    ciphertext_roundtrip, authenticate]
  rfl

theorem typed_attack_result (width : Nat → Nat) (n : Nat) (key : Bool)
    (macKey : TableMAC.Key (width n)) (side state : Bool)
    (code : CryptoOracle.Interactive.Code) (count : Nat) (input : List Bool) :
    ((attack width n code count input).run
      (privacyOracle OneBitEncryption.scheme (TableMAC.scheme width) n key macKey side) state).map Outcome.result =
      ((byteAttack code count input).run (bytePrivacyOracle width n key macKey side) state).map Outcome.result :=
  Program.mapQueries_run_result request AuthenticateResponse.encode _ _ _

theorem byte_attack_result {State : Type*} (code : CryptoOracle.Interactive.Code)
    (count : Nat) (input : List Bool) (oracle : CryptoOracle.Interactive.BitOracle State) (state : State) :
    ((byteAttack code count input).run oracle state).map Outcome.result =
      (CryptoOracle.Interactive.Reification.eval code oracle count
        ⟨state, .running (Configuration.initial input), []⟩).map (fun frame => guess frame.control) := by
  rw [byteAttack, CryptoOracle.Interactive.Reification.decoded_program_run, PMF.map_comp]
  rfl

theorem source_attack_result (width : Nat → Nat) (n : Nat) (key : Bool)
    (macKey : TableMAC.Key (width n)) (side state : Bool)
    (code : CryptoOracle.Interactive.Code) (count : Nat) (input : List Bool) :
    (CryptoOracle.Interactive.Reification.eval code
      (PrivacyMachine.authenticatedOracle (byteEncryptionOracle n key side) macKey) count
        (PrivacyMachine.logicalInitial state input).view).map (fun frame => guess frame.control) =
      ((attack width n code count input).run
        (privacyOracle OneBitEncryption.scheme (TableMAC.scheme width) n key macKey side) state).map Outcome.result := by
  change (CryptoOracle.Interactive.Reification.eval code
    (PrivacyMachine.authenticatedOracle (byteEncryptionOracle n key side) macKey) count
      ⟨(state, []), .running (Configuration.initial input), []⟩).map (fun frame => guess frame.control) = _
  rw [← byte_attack_result, typed_attack_result]
  exact Program.run_state_map_result Prod.fst _ _ (history_projection width n key macKey side)
    (byteAttack code count input) (state, [])

end Foundation.Symmetric.EncryptThenMAC.PrivacyGameCodec
