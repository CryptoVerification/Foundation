import Foundation.Crypto.Semantics.Oracle.QueryMap
import Foundation.Crypto.Semantics.Probability.Facts

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

/-- A one-step invariant holds after every reachable adaptive execution. -/
theorem run_preserves (source : Oracle Request Response State) (invariant : State → Prop)
    (preserves : ∀ state, invariant state → ∀ request answer,
      answer ∈ (source state request).support → invariant answer.1)
    (p : Program Request Response Result) (state : State) (valid : invariant state)
    (out : Outcome Request Response Result State) (support : out ∈ (p.run source state).support) :
    invariant out.state := by
  induction p generalizing state out with
  | done result =>
      rw [run, PMF.mem_support_pure_iff] at support
      subst out
      exact valid
  | query request next ih =>
      rw [run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, ha, ht⟩ := support
      rw [PMF.mem_support_map_iff] at ht
      obtain ⟨tail, ht, rfl⟩ := ht
      exact ih answer.2 answer.1 (preserves state valid request answer ha) tail ht
  | coin next ih =>
      rw [run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, ht⟩ := support
      exact ih bit state valid out ht

/-- If an observation changes only by folding a query and its response, its
final value is determined by the public transcript, even with adaptive queries
and local coins. This is a mathematical observation, not executable observation
code or a resource certificate. -/
theorem run_observe_trace {Observation : Type*}
    (source : Oracle Request Response State) (observe : State → Observation)
    (update : Observation → Request → Response → Observation)
    (step : ∀ state request answer, answer ∈ (source state request).support →
      observe answer.1 = update (observe state) request answer.2)
    (p : Program Request Response Result) (state : State)
    (out : Outcome Request Response Result State) (support : out ∈ (p.run source state).support) :
    observe out.state = out.trace.foldl (fun seen entry => update seen entry.1 entry.2) (observe state) := by
  induction p generalizing state out with
  | done result =>
      rw [run, PMF.mem_support_pure_iff] at support
      subst out
      rfl
  | coin next ih =>
      rw [run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, reachable⟩ := support
      exact ih bit state out reachable
  | query request next ih =>
      rw [run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, reachable, tailSupport⟩ := support
      rw [PMF.mem_support_map_iff] at tailSupport
      obtain ⟨tail, tailSupport, rfl⟩ := tailSupport
      simpa only [List.foldl_cons, ← step state request answer reachable] using
        ih answer.2 answer.1 tail tailSupport

/-- Supported one-step projections lift to complete adaptive executions.
This is only support inclusion, not equality or domination of probabilities. -/
theorem run_support_state_map (project : State → TargetState)
    (source : Oracle Request Response State) (target : Oracle Request Response TargetState)
    (step : ∀ state request answer, answer ∈ (source state request).support →
      (project answer.1, answer.2) ∈ (target (project state) request).support)
    (p : Program Request Response Result) (state : State)
    (out : Outcome Request Response Result State) (support : out ∈ (p.run source state).support) :
    mapState project out ∈ (p.run target (project state)).support := by
  induction p generalizing state out with
  | done result =>
      rw [run, PMF.mem_support_pure_iff] at support
      subst out
      simp [run, mapState]
  | query request next ih =>
      rw [run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, reachable, tailSupport⟩ := support
      rw [PMF.mem_support_map_iff] at tailSupport
      obtain ⟨tail, tailSupport, rfl⟩ := tailSupport
      rw [run, PMF.mem_support_bind_iff]
      refine ⟨(project answer.1, answer.2), step state request answer reachable, ?_⟩
      rw [PMF.mem_support_map_iff]
      exact ⟨mapState project tail, ih answer.2 answer.1 tail tailSupport, rfl⟩
  | coin next ih =>
      rw [run, PMF.mem_support_bind_iff] at support ⊢
      obtain ⟨bit, sampled, tailSupport⟩ := support
      exact ⟨bit, sampled, ih bit state out tailSupport⟩

/-- State erasure may be justified only on a preserved invariant, rather
than on malformed or unreachable representations. Public traces are retained. -/
theorem run_state_map_of_invariant (project : State → TargetState)
    (source : Oracle Request Response State) (target : Oracle Request Response TargetState)
    (invariant : State → Prop)
    (preserves : ∀ state, invariant state → ∀ request answer,
      answer ∈ (source state request).support → invariant answer.1)
    (hOracle : ∀ state, invariant state → ∀ request, (source state request).map
      (fun answer => (project answer.1, answer.2)) = target (project state) request)
    (p : Program Request Response Result) (state : State) (valid : invariant state) :
    (p.run source state).map (mapState project) = p.run target (project state) := by
  induction p generalizing state with
  | done result => simp [run, mapState, PMF.pure_map]
  | query request next ih =>
      rw [run, run, ← hOracle state valid request]
      simp only [PMF.map_bind, PMF.bind_map]
      apply bind_congr_of_support
      intro answer support
      have h := congrArg (fun distribution => distribution.map
        (fun out => { out with trace := (request, answer.2) :: out.trace }))
        (ih answer.2 answer.1 (preserves state valid request answer support))
      simpa only [PMF.map_comp, mapState, Function.comp_def] using h
  | coin next ih =>
      simp only [run, PMF.map_bind]
      congr 1
      funext bit
      exact ih bit state valid

theorem run_state_map (project : State → TargetState)
    (source : Oracle Request Response State) (target : Oracle Request Response TargetState)
    (hOracle : ∀ state request, (source state request).map
      (fun answer => (project answer.1, answer.2)) = target (project state) request)
    (p : Program Request Response Result) (state : State) :
    (p.run source state).map (mapState project) = p.run target (project state) :=
  run_state_map_of_invariant project source target (fun _ => True)
    (fun _ _ _ _ _ => trivial) (fun state _ request => hOracle state request) p state trivial

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
