import Foundation.Crypto.Semantics.Oracle.OneUseSource
import Foundation.Crypto.Semantics.ProcedureSimulation

/-! After acceptance, arbitrary adaptive source execution is independent of
the private key. This public controller retains the actual caller state,
physical response processing and trace, but carries no private key. -/
namespace CryptoOracle.Interactive.SpentSource
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

inductive Control (State : Type u) where
  | source (frame : Configuration State)
  | tagging (saved : Machine.Configuration) (state : State)
      (trace : List (List Bool × List Bool)) (request : List Bool)
      (second : Machine.Tape) (packet : Machine.ResponsePacket.Control)
  | calling (saved : Machine.Configuration) (state : State)
      (trace : List (List Bool × List Bool)) (request : List Bool)
      (second : Machine.Tape) (callback : NativeCallback.Control State)

variable {State : Type u} (code : Code) (oracle : BitOracle State)

noncomputable def step : Control State → PMF (Control State)
  | .source frame => match frame.control with
    | .awaiting saved request => PMF.pure (.tagging saved frame.state frame.reverseTrace request saved.outputTape (.start none))
    | _ => (Reification.timedStep code oracle frame).map .source
  | .tagging saved state trace request second (.returned tape) =>
      PMF.pure (.calling saved state trace request second (.responding (.running { outputTape := tape, halted := true })))
  | .tagging saved state trace request second packet =>
      (Machine.ResponsePacket.step packet).map (.tagging saved state trace request second)
  | .calling _ _ _ _ _ (.source ⟨state, .running machine, trace⟩) =>
      PMF.pure (.source ⟨state, .running machine, trace⟩)
  | .calling saved state trace request second callback =>
      (NativeCallback.step [] code oracle saved state trace request callback).map (.calling saved state trace request second)

def embed (key : Machine.Tape) : Control State → OneUseSource.Control State
  | .source frame => .source true key frame
  | .tagging saved state trace request second packet =>
      .handling true saved state trace request (.tagging key second packet)
  | .calling saved state trace request second callback =>
      .handling true saved state trace request (.calling key second callback)

variable (native : Machine.Program) (key : Machine.Tape)

theorem step_embedding (start : Control State) :
    OneUseSource.step native code oracle (embed key start) = (step code oracle start).map (embed key) := by
  cases start with
  | source frame =>
      cases hc : frame.control <;>
        simp [embed, step, OneUseSource.step, hc, PMF.pure_map, PMF.map_comp, Function.comp_def]
  | tagging saved state trace request second packet =>
      cases packet <;>
        simp [embed, step, OneUseSource.step, CheckedCallback.step, PMF.pure_map,
          PMF.map_comp, Function.comp_def]
  | calling saved state trace request second callback =>
      cases callback with
      | responding component =>
        simp [embed, step, OneUseSource.step, CheckedCallback.step, PMF.map_comp, Function.comp_def]
      | source frame =>
        rcases frame with ⟨currentState, control, currentTrace⟩
        cases control <;>
          simp [embed, step, OneUseSource.step, CheckedCallback.step, NativeCallback.step,
            PMF.pure_map, PMF.map_comp, Function.comp_def]

theorem eval_embedding (fuel : Nat) (start : Control State) :
    TimedExecution.eval (OneUseSource.step native code oracle) fuel (embed key start) =
      (TimedExecution.eval (step code oracle) fuel start).map (embed key) := by
  symm
  exact eval_map _ _ (embed key) (fun start => (step_embedding code oracle native key start).symm) fuel start

/-- An observer can inspect the caller and response-processing state, but
cannot inspect the physical private key. -/
theorem key_independence {Result : Type*} (fuel : Nat) (start : Control State)
    (first second : Machine.Tape) (observe : OneUseSource.Control State → Result)
    (hObserve : ∀ visible, observe (embed first visible) = observe (embed second visible)) :
    (TimedExecution.eval (OneUseSource.step native code oracle) fuel (embed first start)).map observe =
      (TimedExecution.eval (OneUseSource.step native code oracle) fuel (embed second start)).map observe := by
  rw [eval_embedding, eval_embedding, PMF.map_comp, PMF.map_comp]
  congr 1
  funext visible
  exact hObserve visible
def erase : OneUseSource.Control State → Option (Control State)
  | .source true _ frame => some (.source frame)
  | .handling true saved state trace request (.tagging _ second packet) =>
      some (.tagging saved state trace request second packet)
  | .handling true saved state trace request (.calling _ second callback) =>
      some (.calling saved state trace request second callback)
  | _ => none

theorem erase_embed (start : Control State) : erase (embed key start) = some start := by
  cases start <;> rfl

theorem public_distribution (fuel : Nat) (start : Control State) :
    (TimedExecution.eval (OneUseSource.step native code oracle) fuel (embed key start)).map erase =
      (TimedExecution.eval (step code oracle) fuel start).map some := by
  rw [eval_embedding, PMF.map_comp]
  congr 1
  funext next
  exact erase_embed key next

/-- Neither the private key nor the native handler program affects future
public execution after the key has been accepted. -/
theorem public_independence (fuel : Nat) (start : Control State)
    (firstNative secondNative : Machine.Program) (firstKey secondKey : Machine.Tape) :
    (TimedExecution.eval (OneUseSource.step firstNative code oracle) fuel (embed firstKey start)).map erase =
      (TimedExecution.eval (OneUseSource.step secondNative code oracle) fuel (embed secondKey start)).map erase := by
  rw [public_distribution, public_distribution]
theorem no_acceptance (fuel : Nat) (start : Control State) :
    ∀ result ∈ (TimedExecution.eval (OneUseSource.step native code oracle) fuel (embed key start)).support,
      OneUseSource.accepted result = false := by
  rw [eval_embedding]
  intro result hResult
  rw [PMF.mem_support_map_iff] at hResult
  obtain ⟨visible, _, he⟩ := hResult
  subst result
  cases visible <;> rfl
end CryptoOracle.Interactive.SpentSource
