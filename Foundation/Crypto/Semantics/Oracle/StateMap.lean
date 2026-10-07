import Foundation.Crypto.Semantics.Oracle.QueryMap

/-! Project opaque oracle state while preserving results and transcripts.
The source controller never receives the hidden state as a branch input. -/
namespace CryptoOracle.Program
open Foundation.Probability
universe u v w s t
set_option backward.isDefEq.respectTransparency false
variable {Request : Type u} {Response : Type v} {Result : Type w}
  {State : Type s} {TargetState : Type t}

def mapState (project : State → TargetState) (out : Outcome Request Response Result State) :
    Outcome Request Response Result TargetState := ⟨out.result, project out.state, out.trace⟩

theorem run_state_map (project : State → TargetState)
    (source : Oracle Request Response State) (target : Oracle Request Response TargetState)
    (hOracle : ∀ state request, (source state request).map
      (fun answer => (project answer.1, answer.2)) = target (project state) request)
    (p : Program Request Response Result) (state : State) :
    (p.run source state).map (mapState project) = p.run target (project state) := by
  induction p generalizing state with
  | done result => simp [run, mapState, PMF.pure_map]
  | query request next ih =>
      rw [run, run, ← hOracle state request]
      simp only [PMF.map_bind, PMF.bind_map]
      congr 1
      funext answer
      have h := congrArg (fun distribution => distribution.map
        (fun out => { out with trace := (request, answer.2) :: out.trace })) (ih answer.2 answer.1)
      simpa only [PMF.map_comp, mapState, Function.comp_def] using h
  | coin next ih =>
      simp only [run, PMF.map_bind]
      congr 1
      funext bit
      exact ih bit state

theorem run_state_map_result (project : State → TargetState)
    (source : Oracle Request Response State) (target : Oracle Request Response TargetState)
    (hOracle : ∀ state request, (source state request).map
      (fun answer => (project answer.1, answer.2)) = target (project state) request)
    (p : Program Request Response Result) (state : State) :
    (p.run source state).map Outcome.result = (p.run target (project state)).map Outcome.result := by
  have h := congrArg (fun distribution => distribution.map Outcome.result)
    (run_state_map project source target hOracle p state)
  simpa only [PMF.map_comp, mapState, Function.comp_def] using h

theorem mapQueries_run_result {TargetRequest TargetResponse : Type*}
    (request : Request → TargetRequest) (response : TargetResponse → Response)
    (p : Program Request Response Result) (oracle : Oracle TargetRequest TargetResponse State) (state : State) :
    ((p.mapQueries request response).run oracle state).map Outcome.result =
      (p.run (adaptOracle request response oracle) state).map Outcome.result := by
  have h := congrArg (fun distribution => distribution.map Outcome.result)
    (mapQueries_run request response p oracle state)
  simpa only [PMF.map_comp, mapTranscript, Function.comp_def] using h

end CryptoOracle.Program
