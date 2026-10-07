import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegritySourceExecution
import Foundation.Examples.EncryptThenMACIntegrityCallback
import Foundation.Examples.EncryptThenMACIntegrityMachine

namespace Foundation.Symmetric.EncryptThenMAC.IntegritySourceExamples
open Machine Foundation.Probability IntegrityMachine

def haltCode : SourceCode := [.native .halt]

theorem halt_source (oracle : State → Bool → PMF (State × List Bool)) (key : Bool)
    (state : State) (input : List Bool) :
    ∀ final ∈ (TimedExecution.eval (logicalStep haltCode oracle key) 1 (logicalInitial state input)).support,
      CryptoOracle.Interactive.Reification.terminal final.control = true := by
  intro final hFinal
  simp [TimedExecution.eval, logicalStep, logicalInitial, haltCode,
    CryptoOracle.Interactive.Reification.terminal, CryptoOracle.Interactive.Reification.action,
    CryptoOracle.Interactive.transition, Configuration.initial, Instruction.next] at hFinal
  subst final
  rfl

example {width : Nat} (macKey : TableMAC.Key width) (input : List Bool) :
    HaltsWithin haltCode (IntegrityCallbackExamples.oracle macKey) (initial () input)
      (executionBudget width 1) := by
  have hTags : TagLength (IntegrityCallbackExamples.oracle macKey) width := by
    intro state ciphertext answer h
    cases state
    exact IntegrityCallbackExamples.tag_length macKey ciphertext answer h
  exact initialized_source_haltsWithin haltCode _ width hTags 1 () input
    (fun key _ => halt_source _ key () input)

-- A source experiment tracks the hidden signing state, encryption used bit,
-- and signing history inside its oracle, never in the source instruction
-- selector. Its one oracle transition has the atomic experiment semantics.
abbrev SourceState := Nat × Bool × List (Bool × List Bool)
def sourceOracle (key : Bool) (state : SourceState) (request : List Bool) : SourceState × List Bool :=
  if state.2.1 then ((state.1, true, state.2.2), [false])
  else
    let ciphertext := Bool.xor key (request.headD false)
    let answer := IntegrityMachineExamples.oracle state.1 ciphertext
    ((answer.1, true, (ciphertext, answer.2) :: state.2.2), true :: ciphertext :: answer.2)

-- Compare complete configurations and both histories for the four-request
-- example. These path checks supplement the general distribution theorem.
#guard [false, true].all fun key =>
  let start : CryptoOracle.Interactive.Configuration SourceState :=
    ⟨(0, false, []), .running (Configuration.initial [true]), []⟩
  let (source, sourceUsed) := CryptoOracle.Interactive.Reification.simulate
    IntegrityMachineExamples.code (sourceOracle key) key 1000 start
  let (target, targetUsed) := simulate IntegrityMachineExamples.code IntegrityMachineExamples.oracle key 1000 (initial 0 [true])
  match target.control with
  | .source targetKey used control =>
      sourceUsed == 61 && targetUsed == 172 && targetKey == key && used == source.state.2.1 &&
      control == source.control && target.sourceTrace == source.reverseTrace &&
      target.state == source.state.1 && target.signingTrace == source.state.2.2 && terminal target.control
  | _ => false

end Foundation.Symmetric.EncryptThenMAC.IntegritySourceExamples
