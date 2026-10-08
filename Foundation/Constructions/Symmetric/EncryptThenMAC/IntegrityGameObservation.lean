import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityGameCodec

/-! Connect actual native initialization and execution to the typed integrity
attack's full outcome. The public transcript is retained here; identification
with the actual signing history for the MAC forgery game is a separate law. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityGameObservation
open Foundation.Probability CryptoOracle IntegrityGameCodec
set_option backward.isDefEq.respectTransparency false

def SourceStops (width : Nat → Nat) (n : Nat) (macKey : TableMAC.Key (width n))
    (code : Interactive.Code) (count : Nat) (input : List Bool) : Prop :=
  ∀ key ∈ sampleBit.support, Interactive.Reification.HaltsWithin code
    (IntegrityMachine.sourceOracle (byteSigningOracle macKey) key)
    (IntegrityMachine.logicalInitial () input).view count

def observeTyped (width : Nat) (value : Option (Interactive.Configuration (IntegrityMachine.SourceState Unit))) :
    Outcome Bool (Option (Bool × Bits width)) (Bool × Bits width) Bool :=
  match value with
  | some frame => ⟨candidate width frame.control, frame.state.2.1,
      frame.reverseTrace.reverse.map (fun pair => (request pair.1, decodeResponse width pair.2))⟩
  | none => ⟨(false, fun _ => false), false, []⟩

def nativeOutcome (width : Nat) (frame : IntegrityMachine.Frame Unit) :
    Outcome Bool (Option (Bool × Bits width)) (Bool × Bits width) Bool :=
  observeTyped width (IntegrityMachine.sourceView frame)

/-- Real key generation and bounded native execution realize the typed
attack's candidate, exhaustion state and entire public transcript. -/
theorem execution_outcome (width : Nat → Nat) (n : Nat) (macKey : TableMAC.Key (width n))
    (code : Interactive.Code) (count : Nat) (input : List Bool)
    (hStops : SourceStops width n macKey code count input) :
    (IntegrityMachine.eval code (byteSigningOracle macKey)
      (IntegrityMachine.executionBudget (width n) count) (IntegrityMachine.initial () input)).map
        (nativeOutcome (width n)) =
      sampleBit.bind (fun key => (attack width n code count input).run
        (integrityOracle OneBitEncryption.scheme (TableMAC.scheme width) n key macKey) false) := by
  have h := congrArg (fun distribution => distribution.map (observeTyped (width n)))
    (IntegrityMachine.initialized_source_observation code (byteSigningOracle macKey)
      (width n) (signing_length macKey) count () input hStops)
  simp only [PMF.map_comp, Function.comp_def, PMF.map_bind] at h
  change (IntegrityMachine.eval code (byteSigningOracle macKey)
      (IntegrityMachine.executionBudget (width n) count) (IntegrityMachine.initial () input)).map
        (fun frame => observeTyped (width n) (IntegrityMachine.sourceView frame)) = _
  rw [h]
  congr 1
  funext key
  change (Interactive.Reification.eval code (IntegrityMachine.sourceOracle (byteSigningOracle macKey) key)
    count ⟨((), false, []), .running (Machine.Configuration.initial input), []⟩).map
      (fun frame => (⟨candidate (width n) frame.control, frame.state.2.1,
        frame.reverseTrace.reverse.map (fun pair => (request pair.1, decodeResponse (width n) pair.2))⟩ :
          Outcome Bool (Option (Bool × Bits (width n))) (Bool × Bits (width n)) Bool)) = _
  exact (source_attack_run width n key macKey false code count input).symm

theorem execution_halts (width : Nat → Nat) (n : Nat) (macKey : TableMAC.Key (width n))
    (code : Interactive.Code) (count : Nat) (input : List Bool)
    (hStops : SourceStops width n macKey code count input) :
    IntegrityMachine.HaltsWithin code (byteSigningOracle macKey) (IntegrityMachine.initial () input)
      (IntegrityMachine.executionBudget (width n) count) :=
  IntegrityMachine.initialized_source_stops code (byteSigningOracle macKey) (width n)
    (signing_length macKey) count () input hStops

end Foundation.Symmetric.EncryptThenMAC.IntegrityGameObservation
