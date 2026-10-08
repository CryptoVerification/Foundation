import Foundation.Crypto.Semantics.Oracle.RejectionTiming
import Foundation.Constructions.Symmetric.OneTimePad

/-! Arbitrary-width private keys yield the same public return and actual
cost distribution for an invalid request issued by real caller code. -/
namespace Foundation.Examples.RejectionTiming
open Foundation.Probability Foundation.Symmetric CryptoOracle.Interactive TimedExecution
universe u

def code : Code := [.call, .native .halt]

def machine (request : List Bool) (tail : List (Option Bool)) : Machine.Configuration :=
  { outputTape := RequestExport.packetTape [] tail request }

def input {width : Nat} (key : Bits width) (request : List Bool) (tail : List (Option Bool))
    (hMismatch : width ≠ request.length) : Machine.PreparationCheck.FailureInput :=
  ⟨key.toList, request, [], tail, by simpa using hMismatch⟩

theorem machine_active (request : List Bool) (tail : List (Option Bool)) :
    (machine request tail).halted = false := rfl

theorem machine_call (request : List Bool) (tail : List (Option Bool)) :
    code[(machine request tail).pc]? = some .call := rfl

theorem machine_tape {width : Nat} (key : Bits width) (request : List Bool)
    (tail : List (Option Bool)) (hMismatch : width ≠ request.length) :
    (machine request tail).outputTape = RequestExport.packetTape []
      (input key request tail hMismatch).secondTail (input key request tail hMismatch).second := rfl

noncomputable def publicRun {State : Type u} {width : Nat} (native : Machine.Program)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (key : Bits width) (request : List Bool) (tail : List (Option Bool))
    (hMismatch : width ≠ request.length) :=
  let invocation := OneUseSource.rejectedInvocation native code oracle (machine request tail) state trace
    (machine_active request tail) (machine_call request tail) (input key request tail hMismatch)
    (machine_tape key request tail hMismatch)
  (invocation.costed ()).map (fun result =>
    (CryptoOracle.Interactive.RejectionTiming.publicExit (invocation.exit () result.1), result.2))

theorem key_independence {State : Type u} {width : Nat}
    (firstNative secondNative : Machine.Program) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool)) (firstKey secondKey : Bits width)
    (request : List Bool) (tail : List (Option Bool)) (hMismatch : width ≠ request.length) :
    publicRun firstNative oracle state trace firstKey request tail hMismatch =
      publicRun secondNative oracle state trace secondKey request tail hMismatch := by
  have hp := CryptoOracle.Interactive.RejectionTiming.preparation_cost_independence
    firstNative secondNative code code oracle oracle (machine request tail).advance (machine request tail).advance
    state state trace trace request request (input firstKey request tail hMismatch) (input secondKey request tail hMismatch)
    (by simp [input]) rfl rfl rfl
  change CryptoOracle.Interactive.RejectionTiming.costs
      (12 * Machine.PreparationCheck.consumed (input firstKey request tail hMismatch) + 10)
      (CryptoOracle.Interactive.RejectionTiming.initial (input firstKey request tail hMismatch)) =
    CryptoOracle.Interactive.RejectionTiming.costs
      (12 * Machine.PreparationCheck.consumed (input secondKey request tail hMismatch) + 10)
      (CryptoOracle.Interactive.RejectionTiming.initial (input secondKey request tail hMismatch)) at hp
  unfold publicRun
  dsimp only
  rw [CryptoOracle.Interactive.RejectionTiming.rejected_invocation_costs,
    CryptoOracle.Interactive.RejectionTiming.rejected_invocation_costs, hp]
  rfl

end Foundation.Examples.RejectionTiming
