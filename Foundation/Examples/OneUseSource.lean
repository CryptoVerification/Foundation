import Foundation.Crypto.Semantics.Oracle.OneUseSource

/-! Two actual calls after a key is spent. Both return physical rejection
packets and the caller executes its actual halt. The second request comes
from the response tape of the first call. The native program is arbitrary. -/
namespace Foundation.OneUseSourceExamples
open Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u

def code : Code := [.call, .call, .native .halt]

def caller (sourceInput : Machine.Tape) (request : List Bool) (tail : List (Option Bool)) :
    Machine.Configuration :=
  { inputTape := sourceInput, outputTape := RequestExport.packetTape [] tail request }

def afterFirst (sourceInput : Machine.Tape) (request : List Bool) (tail : List (Option Bool)) :=
  { (caller sourceInput request tail).advance with outputTape := ResponseLoading.loaded [false] }

variable {State : Type u} (native : Machine.Program) (oracle : BitOracle State)
    (key sourceInput : Machine.Tape) (state : State) (trace : List (List Bool × List Bool))
    (request : List Bool) (tail : List (Option Bool))

theorem first_call :
    TimedExecution.eval (OneUseSource.step native code oracle) (2 * request.length + 22)
      (.source true key ⟨state, .running (caller sourceInput request tail), trace⟩) =
      PMF.pure (.source true key ⟨state, .running (afterFirst sourceInput request tail), (request, [false]) :: trace⟩) := by
  rw [show 2 * request.length + 22 = (2 * request.length + 4) + 18 by omega,
    TimedExecution.eval_add]
  rw [OneUseSource.call_entry native code oracle true key (caller sourceInput request tail)
    state trace request [] tail rfl rfl rfl, PMF.pure_bind]
  simpa [NativeCallback.resumed, afterFirst] using
    OneUseSource.spent_reply native code oracle (caller sourceInput request tail).advance
      state trace request key (caller sourceInput request tail).outputTape

def final : OneUseSource.Control State :=
  .source true key ⟨state, .running { (afterFirst sourceInput request tail).advance with
    outputTape := ResponseLoading.loaded [false], halted := true },
    ([false], [false]) :: (request, [false]) :: trace⟩

theorem run :
    TimedExecution.eval (OneUseSource.step native code oracle) (2 * request.length + 47)
      (.source true key ⟨state, .running (caller sourceInput request tail), trace⟩) =
      PMF.pure (final key sourceInput state trace request tail) := by
  rw [show 2 * request.length + 47 = (2 * request.length + 22) + 25 by omega,
    TimedExecution.eval_add, first_call, PMF.pure_bind]
  rw [show 25 = (2 * ([false] : List Bool).length + 4) + 19 by rfl, TimedExecution.eval_add]
  rw [OneUseSource.call_entry native code oracle true key (afterFirst sourceInput request tail)
    state ((request, [false]) :: trace) [false] [] [] rfl rfl rfl, PMF.pure_bind]
  simp only [↓reduceIte]
  rw [show 19 = 18 + 1 by rfl, TimedExecution.eval_add, OneUseSource.spent_reply, PMF.pure_bind]
  simp [TimedExecution.eval, OneUseSource.step, NativeCallback.resumed, afterFirst, caller,
    Machine.Configuration.advance, code, Reification.timedStep, Reification.terminal,
    Reification.perform, Reification.action, transition, Machine.Instruction.next, final, PMF.pure_map]

def terminal : OneUseSource.Control State → Bool
  | .source _ _ frame => Reification.terminal frame.control
  | _ => false

theorem source_stops :
    ∀ result ∈ (TimedExecution.eval (OneUseSource.step native code oracle) (2 * request.length + 47)
      (.source true key ⟨state, .running (caller sourceInput request tail), trace⟩)).support,
      terminal result = true := by
  rw [run]
  intro result hResult
  rw [PMF.mem_support_pure_iff] at hResult
  subst result
  rfl

end Foundation.OneUseSourceExamples
