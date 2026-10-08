import Foundation.Crypto.Semantics.Oracle.SpentSource

/-! A real source branches on its response bit, then calls from one of two
instruction positions. Key-independent execution includes both branches and
any subsequent requests, randomness or source computation. -/
namespace Foundation.SpentSourceExamples
open Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false

def code : Code :=
  [.native (.branch .output 5 1 3), .native (.write .output false), .call,
   .native (.write .output true), .call, .native .halt]

variable {State : Type u} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (bit : Bool)

def initial : SpentSource.Control State :=
  .source ⟨state, .running { outputTape := Machine.Tape.ofBits [bit] }, trace⟩

def selected : Machine.Configuration :=
  { pc := if bit then 4 else 2, outputTape := Machine.Tape.ofBits [bit] }

theorem branch_run :
    TimedExecution.eval (SpentSource.step code oracle) 2 (initial state trace bit) =
      PMF.pure (.source ⟨state, .running (selected bit), trace⟩) := by
  cases bit <;>
    simp [TimedExecution.eval, SpentSource.step, initial, selected, code, Reification.timedStep,
      Reification.terminal, Reification.perform, Reification.action, transition, Machine.Instruction.next,
      Machine.Configuration.tape, Machine.Configuration.updateTape, Machine.Configuration.advance,
      Machine.Tape.ofBits, Machine.Tape.write, PMF.pure_map, PMF.pure_bind]

theorem selected_call : code[(selected bit).pc]? = some .call := by cases bit <;> rfl

theorem adaptive_key_independence (fuel : Nat)
    (firstNative secondNative : Machine.Program) (firstKey secondKey : Machine.Tape) :
    (TimedExecution.eval (OneUseSource.step firstNative code oracle) fuel
      (SpentSource.embed firstKey (initial state trace bit))).map SpentSource.erase =
    (TimedExecution.eval (OneUseSource.step secondNative code oracle) fuel
      (SpentSource.embed secondKey (initial state trace bit))).map SpentSource.erase :=
  SpentSource.public_independence code oracle fuel (initial state trace bit) firstNative secondNative firstKey secondKey
end Foundation.SpentSourceExamples
