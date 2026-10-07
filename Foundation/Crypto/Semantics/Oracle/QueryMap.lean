import Foundation.Crypto.Semantics.Oracle.Program

/-! Changing the query interface of an adaptive oracle program. Each source
query becomes exactly one target query. Responses are converted before the
source continuation resumes. The simulation law retains the complete joint
distribution of result, hidden oracle state, and transcript. These functions
are semantic adapters; no CPU bound for their host-language implementations
is inferred. -/
namespace CryptoOracle.Program
open Foundation.Probability
universe u v w x y s
set_option backward.isDefEq.respectTransparency false

variable {Request : Type u} {Response : Type v} {Result : Type w}
  {TargetRequest : Type x} {TargetResponse : Type y}

def mapQueries (request : Request → TargetRequest) (response : TargetResponse → Response) :
    Program Request Response Result → Program TargetRequest TargetResponse Result
  | .done result => .done result
  | .query value next => .query (request value) (fun answer =>
      mapQueries request response (next (response answer)))
  | .coin next => .coin (fun bit => mapQueries request response (next bit))

def mapTranscript {State : Type s} (request : Request → TargetRequest)
    (response : Response → TargetResponse) (out : Outcome Request Response Result State) :
    Outcome TargetRequest TargetResponse Result State :=
  ⟨out.result, out.state, out.trace.map (fun pair => (request pair.1, response pair.2))⟩

noncomputable def adaptOracle {State : Type s} (request : Request → TargetRequest)
    (response : TargetResponse → Response) (oracle : Oracle TargetRequest TargetResponse State) :
    Oracle Request Response State := fun state value =>
  (oracle state (request value)).map (fun answer => (answer.1, response answer.2))

/-- No injectivity, surjectivity, or encoding inverse is needed: both sides
are compared in the common interface of target requests and source responses. -/
theorem mapQueries_run {State : Type s} (request : Request → TargetRequest)
    (response : TargetResponse → Response) (p : Program Request Response Result)
    (oracle : Oracle TargetRequest TargetResponse State) (state : State) :
    ((p.mapQueries request response).run oracle state).map (mapTranscript id response) =
      (p.run (adaptOracle request response oracle) state).map (mapTranscript request id) := by
  induction p generalizing state with
  | done result => simp [mapQueries, run, mapTranscript, PMF.pure_map]
  | query value next ih =>
      simp only [mapQueries, run, adaptOracle, PMF.map_bind, PMF.bind_map,
        PMF.map_comp]
      congr 1
      funext answer
      have h := ih (response answer.2) answer.1
      have hm := congrArg (fun distribution => distribution.map
        (fun out => { out with trace := (request value, response answer.2) :: out.trace })) h
      simpa only [PMF.map_comp, mapTranscript, List.map_cons, Function.comp_def, id_eq] using hm
  | coin next ih =>
      simp only [mapQueries, run, PMF.map_bind]
      congr 1
      funext bit
      exact ih bit state

theorem mapQueries_queries (request : Request → TargetRequest)
    (response : TargetResponse → Response) {p : Program Request Response Result} {q : Nat}
    (h : p.BoundedQueries q) : (p.mapQueries request response).BoundedQueries q := by
  induction h with
  | done result q => exact .done _ _
  | query value next q h ih => exact .query _ _ q (fun answer => ih (response answer))
  | coin next q h ih => exact .coin _ q ih

theorem mapQueries_id (p : Program Request Response Result) : p.mapQueries id id = p := by
  induction p with
  | done result => rfl
  | query value next ih => simp only [mapQueries, id_eq]; congr; funext answer; exact ih answer
  | coin next ih => simp only [mapQueries]; congr; funext bit; exact ih bit

theorem mapQueries_comp {FinalRequest FinalResponse : Type*}
    (request : Request → TargetRequest) (response : TargetResponse → Response)
    (request' : TargetRequest → FinalRequest) (response' : FinalResponse → TargetResponse)
    (p : Program Request Response Result) :
    (p.mapQueries request response).mapQueries request' response' =
      p.mapQueries (request' ∘ request) (response ∘ response') := by
  induction p with
  | done result => rfl
  | query value next ih =>
      simp only [mapQueries, Function.comp_def]
      congr
      funext answer
      exact ih (response (response' answer))
  | coin next ih => simp only [mapQueries]; congr; funext bit; exact ih bit

end CryptoOracle.Program
