import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacySourceProcedure

/-! Complete native privacy experiments, packaged through the reusable
initialization/consumer contract. The target encryption key is sampled by
its external encryption game, as in the registered native privacy backend. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyContractSecurity
open Foundation.Probability CryptoOracle
set_option backward.isDefEq.respectTransparency false

noncomputable def game (width : Nat → Nat) (n : Nat) (side : Bool)
    (code : Interactive.Code) (count : Nat) (input : List Bool)
    (hStops : ∀ (encryptionKey : Bool) (macKey : TableMAC.Key (width n)),
      Interactive.Reification.HaltsWithin code
        (PrivacyMachine.authenticatedOracle (PrivacyGameCodec.byteEncryptionOracle n encryptionKey side) macKey)
        (PrivacyMachine.logicalInitial false input).view count) : PMF (Bool × Nat) :=
  (OneBitEncryption.scheme.keygen n).bind (fun encryptionKey =>
    (PrivacyMachine.sourceExperiment code (PrivacyGameCodec.byteEncryptionOracle n encryptionKey side)
      width n count false input (hStops encryptionKey)).publicCost ())

theorem game_eq (width : Nat → Nat) (n : Nat) (side : Bool)
    (code : Interactive.Code) (count : Nat) (input : List Bool)
    (hStops : ∀ (encryptionKey : Bool) (macKey : TableMAC.Key (width n)),
      Interactive.Reification.HaltsWithin code
        (PrivacyMachine.authenticatedOracle (PrivacyGameCodec.byteEncryptionOracle n encryptionKey side) macKey)
        (PrivacyMachine.logicalInitial false input).view count) :
    game width n side code count input hStops =
      (NativePrivacyGame.game width n side code count input).map
        (fun bit => (bit, PrivacyMachine.executionBudget (width n) count)) := by
  unfold game NativePrivacyGame.game
  simp only [PrivacyMachine.sourceExperiment_publicCost, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- The common padded-horizon result and cost law is perfectly private for
arbitrary finite source code with CPU witnesses for both challenge sides. -/
theorem perfect (width : Nat → Nat) (n : Nat) (code : Interactive.Code) (count : Nat) (input : List Bool)
    (hStops : ∀ (side encryptionKey : Bool) (macKey : TableMAC.Key (width n)),
      Interactive.Reification.HaltsWithin code
        (PrivacyMachine.authenticatedOracle (PrivacyGameCodec.byteEncryptionOracle n encryptionKey side) macKey)
        (PrivacyMachine.logicalInitial false input).view count) :
    game width n false code count input (hStops false) =
      game width n true code count input (hStops true) := by
  rw [game_eq, game_eq,
    NativePrivacyGame.game_eq_encryption width n false code count input
      (fun encryptionKey _ macKey _ => hStops false encryptionKey macKey),
    NativePrivacyGame.game_eq_encryption width n true code count input
      (fun encryptionKey _ macKey _ => hStops true encryptionKey macKey)]
  rw [OneBitEncryption.game_perfect]

end Foundation.Symmetric.EncryptThenMAC.PrivacyContractSecurity
