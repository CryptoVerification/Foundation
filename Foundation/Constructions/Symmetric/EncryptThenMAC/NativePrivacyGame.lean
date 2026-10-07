import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyGameCodec

/-! Actual native privacy reduction realizes the existing typed privacy and
encryption games. The external experiment samples its encryption key; the
reduction samples its authentication key using its own charged native code. -/
namespace Foundation.Symmetric.EncryptThenMAC.NativePrivacyGame
open Machine Foundation.Probability CryptoOracle
open PrivacyGameCodec
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- A source CPU witness for this experiment, uniform over the supported
private authentication keys. This uses the existing native source evaluator. -/
def SourceStops (width : Nat → Nat) (n : Nat) (key side : Bool)
    (code : CryptoOracle.Interactive.Code) (count : Nat) (input : List Bool) : Prop :=
  ∀ macKey ∈ ((TableMAC.scheme width).keygen n).support,
    CryptoOracle.Interactive.Reification.HaltsWithin code
      (PrivacyMachine.authenticatedOracle (byteEncryptionOracle n key side) macKey)
      (PrivacyMachine.logicalInitial false input).view count

theorem initialized_result (width : Nat → Nat) (n : Nat) (key side : Bool)
    (code : CryptoOracle.Interactive.Code) (count : Nat) (input : List Bool)
    (hStops : SourceStops width n key side code count input) :
    (PrivacyMachine.eval code (byteEncryptionOracle n key side)
      (PrivacyMachine.executionBudget (width n) count)
      (PrivacyMachine.initial false (List.replicate (2 * width n) true) input)).map nativeGuess =
      ((TableMAC.scheme width).keygen n).bind (fun macKey =>
        ((attack width n code count input).run
          (privacyOracle OneBitEncryption.scheme (TableMAC.scheme width) n key macKey side) false).map Outcome.result) := by
  have h := congrArg (fun distribution => distribution.map viewGuess)
    (PrivacyMachine.initialized_source_observation code (byteEncryptionOracle n key side)
      width n count false input hStops)
  simp only [PMF.map_comp, Function.comp_def, viewGuess_sourceView, PMF.map_bind] at h
  rw [h]
  congr 1
  funext macKey
  change (CryptoOracle.Interactive.Reification.eval code
    (PrivacyMachine.authenticatedOracle (byteEncryptionOracle n key side) macKey) count
      (PrivacyMachine.logicalInitial false input).view).map (fun frame => guess frame.control) = _
  exact source_attack_result width n key macKey side false code count input

noncomputable def game (width : Nat → Nat) (n : Nat) (side : Bool)
    (code : CryptoOracle.Interactive.Code) (count : Nat) (input : List Bool) : PMF Bool :=
  (OneBitEncryption.scheme.keygen n).bind (fun key =>
    (PrivacyMachine.eval code (byteEncryptionOracle n key side)
      (PrivacyMachine.executionBudget (width n) count)
      (PrivacyMachine.initial false (List.replicate (2 * width n) true) input)).map nativeGuess)

/-- Exact Boolean experiment law, for each chosen-plaintext challenge side.
The native sampler and source output convention are part of the theorem. -/
theorem game_eq_privacy (width : Nat → Nat) (n : Nat) (side : Bool)
    (code : CryptoOracle.Interactive.Code) (count : Nat) (input : List Bool)
    (hStops : ∀ key ∈ (OneBitEncryption.scheme.keygen n).support,
      SourceStops width n key side code count input) :
    game width n side code count input =
      privacyGame OneBitEncryption.scheme (TableMAC.scheme width) n side (attack width n code count input) := by
  unfold game privacyGame
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext key hKey
  exact initialized_result width n key side code count input (hStops key hKey)

/-- The concrete native reduction therefore realizes the existing semantic
reduction attack in the encryption game, with no security loss from codecs. -/
theorem game_eq_encryption (width : Nat → Nat) (n : Nat) (side : Bool)
    (code : CryptoOracle.Interactive.Code) (count : Nat) (input : List Bool)
    (hStops : ∀ key ∈ (OneBitEncryption.scheme.keygen n).support,
      SourceStops width n key side code count input) :
    game width n side code count input =
      encryptionGame OneBitEncryption.scheme n side
        (privacyReduction OneBitEncryption.scheme (TableMAC.scheme width) n (attack width n code count input)) :=
  (game_eq_privacy width n side code count input hStops).trans
    (privacyGame_eq OneBitEncryption.scheme (TableMAC.scheme width) n side _)

theorem halts (width : Nat → Nat) (n : Nat) (key side : Bool)
    (code : CryptoOracle.Interactive.Code) (count : Nat) (input : List Bool)
    (hStops : SourceStops width n key side code count input) :
    PrivacyMachine.HaltsWithin code (byteEncryptionOracle n key side)
      (PrivacyMachine.initial false (List.replicate (2 * width n) true) input)
      (PrivacyMachine.executionBudget (width n) count) :=
  PrivacyMachine.initialized_source_stops code (byteEncryptionOracle n key side) width n count false input hStops

/-- Distinguishing advantage of the actual bounded native experiments. -/
noncomputable def advantage (width : Nat → Nat) (n : Nat)
    (code : CryptoOracle.Interactive.Code) (count : Nat) (input : List Bool) : ℝ≥0∞ :=
  probabilityGap (eventProb (game width n false code count input) (· = true))
    (eventProb (game width n true code count input) (· = true))

/-- The native implementation introduces no additional distinguishing loss.
Both challenge experiments must carry their actual source stopping evidence. -/
theorem advantage_eq (width : Nat → Nat) (n : Nat)
    (code : CryptoOracle.Interactive.Code) (count : Nat) (input : List Bool)
    (hStops : ∀ side key, key ∈ (OneBitEncryption.scheme.keygen n).support →
      SourceStops width n key side code count input) :
    advantage width n code count input =
      (encryptionGoal OneBitEncryption.scheme).advantage n ()
        (privacyReduction OneBitEncryption.scheme (TableMAC.scheme width) n
          (attack width n code count input)) := by
  unfold advantage
  rw [game_eq_encryption width n false code count input (hStops false),
    game_eq_encryption width n true code count input (hStops true)]
  rfl

end Foundation.Symmetric.EncryptThenMAC.NativePrivacyGame
