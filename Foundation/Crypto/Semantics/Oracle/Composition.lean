import Foundation.Crypto.Semantics.Oracle.Program

/-! Sequencing and inlining for the existing oracle program syntax.
Inlining can replace one high-level call by multiple lower-level calls while
sharing oracle state. It does not charge CPU time to host continuations.
-/
namespace CryptoOracle.Program

open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
universe u v w x y s

variable {Request : Type u} {Response : Type v} {Result : Type w}
  {NextResult : Type x} {State : Type s}

def bind : Program Request Response Result →
    (Result → Program Request Response NextResult) → Program Request Response NextResult
  | .done result, next => next result
  | .query request more, next => .query request (fun response => bind (more response) next)
  | .coin more, next => .coin (fun bit => bind (more bit) next)

theorem run_bind (p : Program Request Response Result)
    (next : Result → Program Request Response NextResult)
    (oracle : Oracle Request Response State) (state : State) :
    (p.bind next).run oracle state =
      (p.run oracle state).bind (fun first =>
        ((next first.result).run oracle first.state).map (fun last =>
          { last with trace := first.trace ++ last.trace })) := by
  induction p generalizing state with
  | done result =>
      simp only [Program.bind, run, PMF.pure_bind, List.nil_append]
      change _ = PMF.map id _
      rw [PMF.map_id]
  | query request more ih =>
      simp only [bind, run, PMF.bind_map, PMF.bind_bind,
        Function.comp_def, List.cons_append]
      congr 1
      funext answer
      rw [ih answer.2 answer.1]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  | coin more ih =>
      simp only [bind, run, PMF.bind_bind]
      congr 1
      funext bit
      exact ih bit state

theorem BoundedQueries.bind {p : Program Request Response Result} {q r : Nat}
    (hp : p.BoundedQueries q) (next : Result → Program Request Response NextResult)
    (hn : ∀ result, (next result).BoundedQueries r) :
    (p.bind next).BoundedQueries (q + r) := by
  induction hp with
  | done result q => exact (hn result).mono (by omega)
  | query request more q hp ih =>
      simpa only [Program.bind, Nat.add_right_comm] using
        BoundedQueries.query request (fun response => (more response).bind next) (q + r) ih
  | coin more q hp ih => exact .coin _ (q + r) ih

variable {TargetRequest : Type x} {TargetResponse : Type y}

def inline (handler : Request → Program TargetRequest TargetResponse Response) :
    Program Request Response Result → Program TargetRequest TargetResponse Result
  | .done result => .done result
  | .query request next => (handler request).bind (fun response => inline handler (next response))
  | .coin next => .coin (fun bit => inline handler (next bit))

def resultState (out : Outcome Request Response Result State) : State × Result :=
  (out.state, out.result)

noncomputable def implementedOracle
    (handler : Request → Program TargetRequest TargetResponse Response)
    (oracle : Oracle TargetRequest TargetResponse State) : Oracle Request Response State :=
  fun state request => ((handler request).run oracle state).map resultState

/-- Internal query histories differ across the two interfaces. The joint final
state and result agree exactly; high-level traces are not exposed as low-level
traces or charged as if they were machine operations. -/
theorem inline_run (handler : Request → Program TargetRequest TargetResponse Response)
    (p : Program Request Response Result) (oracle : Oracle TargetRequest TargetResponse State)
    (state : State) :
    ((inline handler p).run oracle state).map resultState =
      (p.run (implementedOracle handler oracle) state).map resultState := by
  induction p generalizing state with
  | done result => simp [inline, run, resultState, PMF.pure_map]
  | query request next ih =>
      simp only [inline, run_bind, run, implementedOracle, PMF.map_bind,
        PMF.bind_map, PMF.map_comp, Function.comp_def, resultState]
      congr 1
      funext first
      exact ih first.result first.state
  | coin next ih =>
      simp only [inline, run, PMF.map_bind]
      congr 1
      funext bit
      exact ih bit state

/-- A stateful procedure receives only its own private state. The target oracle
state belongs to the interpreter and cannot be inspected by the procedure. -/
noncomputable def statefulOracle {PrivateState : Type*}
    (procedure : PrivateState → Request →
      Program TargetRequest TargetResponse (PrivateState × Response))
    (oracle : Oracle TargetRequest TargetResponse State) :
    Oracle Request Response (PrivateState × State) :=
  fun (privateState, targetState) request =>
    ((procedure privateState request).run oracle targetState).map fun outcome =>
      ((outcome.result.1, outcome.state), outcome.result.2)

/-- Compile private bookkeeping into the existing syntax, while keeping the
underlying oracle state opaque and shared across all expanded calls. -/
def inlineState {PrivateState : Type*}
    (procedure : PrivateState → Request →
      Program TargetRequest TargetResponse (PrivateState × Response)) :
    PrivateState → Program Request Response Result →
      Program TargetRequest TargetResponse (PrivateState × Result)
  | privateState, .done result => .done (privateState, result)
  | privateState, .query request next =>
      (procedure privateState request).bind (fun answer =>
        inlineState procedure answer.1 (next answer.2))
  | privateState, .coin next => .coin (fun bit => inlineState procedure privateState (next bit))

/-- State compilation preserves the joint final oracle state, private state
and result. The internal and external transcripts deliberately have different
query units; no CPU or storage cost follows from this equation alone. -/
theorem inlineState_run {PrivateState : Type*}
    (procedure : PrivateState → Request →
      Program TargetRequest TargetResponse (PrivateState × Response))
    (p : Program Request Response Result) (oracle : Oracle TargetRequest TargetResponse State)
    (privateState : PrivateState) (state : State) :
    ((inlineState procedure privateState p).run oracle state).map resultState =
      (p.run (statefulOracle procedure oracle) (privateState, state)).map
        (fun out => (out.state.2, (out.state.1, out.result))) := by
  induction p generalizing privateState state with
  | done result => simp [inlineState, run, resultState, PMF.pure_map]
  | coin next ih =>
      simp only [inlineState, run, PMF.map_bind]
      congr 1
      funext bit
      exact ih bit privateState state
  | query request next ih =>
      simp only [inlineState, run_bind, run, statefulOracle, PMF.map_bind,
        PMF.bind_map, PMF.map_comp, Function.comp_def, resultState]
      congr 1
      funext first
      exact ih first.result.2 first.result.1 first.state

/-- Stateful inlining charges every actual backend call, including those used
for local draws. Pure private bookkeeping is not charged as a machine step. -/
theorem inlineState_queries {PrivateState : Type*}
    (procedure : PrivateState → Request →
      Program TargetRequest TargetResponse (PrivateState × Response))
    (calls : Nat) (cost : ∀ state request, (procedure state request).BoundedQueries calls)
    {p : Program Request Response Result} {q : Nat} (bound : p.BoundedQueries q)
    (privateState : PrivateState) : (inlineState procedure privateState p).BoundedQueries (q * calls) := by
  induction bound generalizing privateState with
  | done result q => exact .done _ _
  | coin next q bound ih => exact .coin _ _ (fun bit => ih bit privateState)
  | query request next q bound ih =>
      simp only [inlineState]
      simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        (cost privateState request).bind
          (fun answer => inlineState procedure answer.1 (next answer.2))
          (fun answer => ih answer.2 answer.1)

end CryptoOracle.Program
