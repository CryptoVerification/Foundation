import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegritySourceProcedure
import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityBackend
import Foundation.Constructions.Symmetric.EncryptThenMAC.TableMACSecurity

/-! The finite integrity compiler realizes the common whole-machine contract.
The external MAC game samples the authentication key; the native controller
samples the encryption key and records the actual signing history. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityBackend
open Foundation.Probability CryptoOracle IntegrityGameCodec IntegrityGameObservation
set_option backward.isDefEq.respectTransparency false

theorem contract_stops (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (hExec : SourceExecutes width code r) (n : Nat) (macKey : TableMAC.Key (width n))
    (key : Bool) :
    ∀ final ∈ (TimedExecution.eval
      (IntegrityMachine.logicalStep (compiler.run code).source (byteSigningOracle macKey) key)
      (r.count n) (IntegrityMachine.logicalInitial () (r.input n))).support,
      Interactive.Reification.terminal final.control = true := by
  have hm : macKey ∈ ((TableMAC.scheme width).keygen n).support := by
    rw [TableMAC.keygen_independent, TableMAC.uniform_pair]
    exact PMF.mem_support_uniformOfFintype macKey
  exact IntegrityMachine.logical_stops_of_source code (byteSigningOracle macKey) key
    (r.count n) (IntegrityMachine.logicalInitial () (r.input n))
    (hExec.2.2 n macKey hm key (PMF.mem_support_uniformOfFintype key))

noncomputable def compiledExperiment (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (hExec : SourceExecutes width code r) (n : Nat) (macKey : TableMAC.Key (width n)) :=
  IntegrityMachine.sourceExperiment (compiler.run code).source (byteSigningOracle macKey)
    (width n) (signing_length macKey) (r.count n) () (r.input n)
    (contract_stops width code r hExec n macKey) (NativeIntegrityGame.nativeRecord (width n))

theorem compiledExperiment_budget (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (hExec : SourceExecutes width code r) (n : Nat) (macKey : TableMAC.Key (width n)) :
    (compiledExperiment width code r hExec n macKey).procedure.budget () =
      IntegrityMachine.executionBudget (width n) (r.count n) := rfl

noncomputable def compiledGame (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (hExec : SourceExecutes width code r) (n : Nat) :=
  ((TableMAC.scheme width).keygen n).bind (fun macKey =>
    ((compiledExperiment width code r hExec n macKey).publicCost ()).map
      (fun result => ((macKey, result.1), result.2)))

/-- Equality includes the actual signing transcript and the charged horizon. -/
theorem compiledGame_eq (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (hExec : SourceExecutes width code r) (n : Nat) :
    compiledGame width code r hExec n =
      (NativeIntegrityGame.game width n (compiler.run code).source (r.count n) (r.input n)).map
        (fun record => (record, IntegrityMachine.executionBudget (width n) (r.count n))) := by
  simp only [compiledGame, compiledExperiment, IntegrityMachine.sourceExperiment_publicCost,
    NativeIntegrityGame.game, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Existing cryptographic realization is preserved by the reusable contract.
Compilation still emits only the finite source instruction list. -/
theorem compiledGame_realizes (width : Nat → Nat) (F A) (code : Interactive.Code) (r : Profile)
    (hExec : SourceExecutes width code r) (hReal : SourceRealizes width F A code r) (n : Nat) :
    compiledGame width code r hExec n =
      (macGame OneBitEncryption.scheme (TableMAC.scheme width) n
        ((transform width).mapAdversaryFamily F A n)).map
        (fun record => (record, IntegrityMachine.executionBudget (width n) (r.count n))) := by
  rw [compiledGame_eq]
  exact congrArg (fun distribution => distribution.map
    (fun record => (record, IntegrityMachine.executionBudget (width n) (r.count n))))
    (compiled_realizes width F A code r hExec hReal n)

end Foundation.Symmetric.EncryptThenMAC.IntegrityBackend
