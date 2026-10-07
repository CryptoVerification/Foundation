import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityHistory
import Foundation.Constructions.Symmetric.EncryptThenMAC.Security

/-! The MAC forgery record uses the real signing history, rather than an
invented transcript. Bounded native execution realizes the semantic reduction. -/
namespace Foundation.Symmetric.EncryptThenMAC.NativeIntegrityGame
open Foundation.Probability CryptoOracle IntegrityGameCodec IntegrityGameObservation
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Candidate and chronologically ordered actual signing history. -/
def nativeRecord (width : Nat) (frame : IntegrityMachine.Frame Unit) :
    (Bool × Bits width) × List (Bool × Bits width) :=
  ((nativeOutcome width frame).result, IntegrityMachine.signedHistory width frame.signingTrace)

theorem supported_record (width : Nat → Nat) (n : Nat) (macKey : TableMAC.Key (width n))
    (code : Interactive.Code) (count : Nat) (input : List Bool)
    (hStops : SourceStops width n macKey code count input)
    (frame : IntegrityMachine.Frame Unit)
    (hFrame : frame ∈ (IntegrityMachine.eval code (byteSigningOracle macKey)
      (IntegrityMachine.executionBudget (width n) count) (IntegrityMachine.initial () input)).support) :
    nativeRecord (width n) frame =
      integrityRecord OneBitEncryption.scheme (TableMAC.scheme width) (nativeOutcome (width n) frame) := by
  have ht := execution_halts width n macKey code count input hStops frame hFrame
  have hh := IntegrityMachine.initialized_native_history code (byteSigningOracle macKey)
    (width n) (signing_length macKey) count () input hStops frame hFrame
  cases hc : frame.control <;> simp only [IntegrityMachine.terminal, hc, Bool.false_eq_true] at ht
  simp [nativeRecord, integrityRecord, nativeOutcome, observeTyped,
    IntegrityMachine.sourceView, hc, hh, IntegrityMachine.publicHistory, List.filterMap_map]

theorem execution_record (width : Nat → Nat) (n : Nat) (macKey : TableMAC.Key (width n))
    (code : Interactive.Code) (count : Nat) (input : List Bool)
    (hStops : SourceStops width n macKey code count input) :
    (IntegrityMachine.eval code (byteSigningOracle macKey)
      (IntegrityMachine.executionBudget (width n) count) (IntegrityMachine.initial () input)).map
        (nativeRecord (width n)) =
      sampleBit.bind (fun key => ((attack width n code count input).run
        (integrityOracle OneBitEncryption.scheme (TableMAC.scheme width) n key macKey) false).map
          (integrityRecord OneBitEncryption.scheme (TableMAC.scheme width))) := by
  have hr : (IntegrityMachine.eval code (byteSigningOracle macKey)
      (IntegrityMachine.executionBudget (width n) count) (IntegrityMachine.initial () input)).map
        (nativeRecord (width n)) =
      (IntegrityMachine.eval code (byteSigningOracle macKey)
      (IntegrityMachine.executionBudget (width n) count) (IntegrityMachine.initial () input)).map
        (fun frame => integrityRecord OneBitEncryption.scheme (TableMAC.scheme width) (nativeOutcome (width n) frame)) := by
    rw [PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
    congr 1
    funext frame hFrame
    exact congrArg PMF.pure (supported_record width n macKey code count input hStops frame hFrame)
  have h := congrArg (fun p => p.map (integrityRecord OneBitEncryption.scheme (TableMAC.scheme width)))
    (execution_outcome width n macKey code count input hStops)
  simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at h
  exact hr.trans h

noncomputable def game (width : Nat → Nat) (n : Nat)
    (code : Interactive.Code) (count : Nat) (input : List Bool) :
    PMF (MACRecord OneBitEncryption.scheme (TableMAC.scheme width) n) :=
  ((TableMAC.scheme width).keygen n).bind fun macKey =>
    (IntegrityMachine.eval code (byteSigningOracle macKey)
      (IntegrityMachine.executionBudget (width n) count) (IntegrityMachine.initial () input)).map
        (fun frame => (macKey, nativeRecord (width n) frame))

theorem game_eq (width : Nat → Nat) (n : Nat)
    (code : Interactive.Code) (count : Nat) (input : List Bool)
    (hStops : ∀ macKey ∈ ((TableMAC.scheme width).keygen n).support,
      SourceStops width n macKey code count input) :
    game width n code count input =
      macGame OneBitEncryption.scheme (TableMAC.scheme width) n
        (integrityReduction OneBitEncryption.scheme (TableMAC.scheme width) n (attack width n code count input)) := by
  rw [← integrityGame_project]
  unfold game integrityGame
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [PMF.bind_comm]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext macKey hKey
  have h := congrArg (fun p => p.map (fun record => (macKey, record)))
    (execution_record width n macKey code count input (hStops macKey hKey))
  simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, OneBitEncryption.scheme] using h

noncomputable def advantage (width : Nat → Nat) (n : Nat)
    (code : Interactive.Code) (count : Nat) (input : List Bool) : ℝ≥0∞ :=
  eventProb (game width n code count input)
    (fun record => macWins OneBitEncryption.scheme (TableMAC.scheme width) record.1 record.2)

theorem advantage_eq (width : Nat → Nat) (n : Nat)
    (code : Interactive.Code) (count : Nat) (input : List Bool)
    (hStops : ∀ macKey ∈ ((TableMAC.scheme width).keygen n).support,
      SourceStops width n macKey code count input) :
    advantage width n code count input =
      macAdvantage OneBitEncryption.scheme (TableMAC.scheme width) n
        (integrityReduction OneBitEncryption.scheme (TableMAC.scheme width) n (attack width n code count input)) := by
  rw [advantage, macAdvantage, game_eq width n code count input hStops]

end Foundation.Symmetric.EncryptThenMAC.NativeIntegrityGame
