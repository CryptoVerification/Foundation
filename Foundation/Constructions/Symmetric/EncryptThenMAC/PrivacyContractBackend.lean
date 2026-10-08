import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyContractSecurity
import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyBackend
import Foundation.Constructions.Symmetric.EncryptThenMAC.TableMACSecurity

/-! Attach reusable initialization/consumer contracts to the existing finite
privacy compiler and its CPU/resource certificates. Compilation still emits
only the same source instruction list, never the logical execution tree. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyBackend
open Foundation.Probability CryptoOracle CryptoLogic.General
set_option backward.isDefEq.respectTransparency false

theorem keygen_support (width : Nat → Nat) (n : Nat) (key : TableMAC.Key (width n)) :
    key ∈ ((TableMAC.scheme width).keygen n).support := by
  rw [TableMAC.keygen_independent, TableMAC.uniform_pair]
  exact PMF.mem_support_uniformOfFintype key

theorem contract_stops (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (hExec : SourceExecutes width code r) (n : Nat) (side encryptionKey : Bool)
    (macKey : TableMAC.Key (width n)) :
    Interactive.Reification.HaltsWithin (compiler.run code).source
      (PrivacyMachine.authenticatedOracle (PrivacyGameCodec.byteEncryptionOracle n encryptionKey side) macKey)
      (PrivacyMachine.logicalInitial false (r.input n)).view (r.count n) := by
  have he : encryptionKey ∈ (OneBitEncryption.scheme.keygen n).support :=
    PMF.mem_support_uniformOfFintype encryptionKey
  exact hExec.2.2 n side encryptionKey he macKey (keygen_support width n macKey)

noncomputable def compiledExperiment (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (hExec : SourceExecutes width code r) (n : Nat) (side encryptionKey : Bool) :=
  PrivacyMachine.sourceExperiment (compiler.run code).source
    (PrivacyGameCodec.byteEncryptionOracle n encryptionKey side) width n (r.count n) false (r.input n)
    (contract_stops width code r hExec n side encryptionKey)

theorem compiledExperiment_budget (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (hExec : SourceExecutes width code r) (n : Nat) (side encryptionKey : Bool) :
    (compiledExperiment width code r hExec n side encryptionKey).procedure.budget () =
      PrivacyMachine.executionBudget (width n) (r.count n) := rfl

noncomputable def compiledGame (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (hExec : SourceExecutes width code r) (n : Nat) (side : Bool) :=
  PrivacyContractSecurity.game width n side (compiler.run code).source (r.count n) (r.input n)
    (contract_stops width code r hExec n side)

theorem compiledGame_eq (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (hExec : SourceExecutes width code r) (n : Nat) (side : Bool) :
    compiledGame width code r hExec n side =
      (NativePrivacyGame.game width n side (compiler.run code).source (r.count n) (r.input n)).map
        (fun bit => (bit, PrivacyMachine.executionBudget (width n) (r.count n))) :=
  PrivacyContractSecurity.game_eq _ _ _ _ _ _ _

/-- The existing certified compiler's realization now also carries the
reusable whole-machine contract and its common charged execution horizon. -/
theorem compiledGame_realizes (width : Nat → Nat) (F A) (code : Interactive.Code) (r : Profile)
    (hExec : SourceExecutes width code r) (hReal : SourceRealizes width F A code r)
    (n : Nat) (side : Bool) :
    compiledGame width code r hExec n side =
      (encryptionGame OneBitEncryption.scheme n side
        ((transform width).mapAdversaryFamily F A n)).map
        (fun bit => (bit, PrivacyMachine.executionBudget (width n) (r.count n))) := by
  rw [compiledGame_eq]
  have h := compiled_realizes width F A code r hExec hReal n side
  exact congrArg (fun distribution => distribution.map
    (fun bit => (bit, PrivacyMachine.executionBudget (width n) (r.count n)))) h

theorem compiledGame_perfect (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (hExec : SourceExecutes width code r) (n : Nat) :
    compiledGame width code r hExec n false = compiledGame width code r hExec n true :=
  PrivacyContractSecurity.perfect width n (compiler.run code).source (r.count n) (r.input n)
    (contract_stops width code r hExec n)

end Foundation.Symmetric.EncryptThenMAC.PrivacyBackend
