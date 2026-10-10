import Foundation.Crypto.Semantics.Oracle.QueryMap

/-! Stop before the first request satisfying a public predicate. The result
records whether that request would occur in the original complete interaction.
Stopping is used only to analyze bad-event probabilities, not to weaken games. -/
namespace CryptoOracle.Program

open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Request Response Result State : Type}

def stopBefore (hit : Request → Bool) : Program Request Response Result →
    Program Request Response Bool
  | .done _ => .done false
  | .query request next => if hit request then .done true
      else .query request (fun response => stopBefore hit (next response))
  | .coin next => .coin (fun bit => stopBefore hit (next bit))

/-- Stopping preserves the probability of ever making a marked request,
even when the original program continues adaptively after that request. -/
theorem stopBefore_run (hit : Request → Bool) (program : Program Request Response Result)
    (oracle : Oracle Request Response State) (state : State) :
    ((stopBefore hit program).run oracle state).map Outcome.result =
      (program.run oracle state).map (fun out => out.trace.any (fun e => hit e.1)) := by
  induction program generalizing state with
  | done result => simp [stopBefore, run, PMF.pure_map]
  | coin next ih =>
      simp only [stopBefore, run, PMF.map_bind]
      congr 1
      funext bit
      exact ih bit state
  | query request next ih =>
      by_cases hh : hit request = true
      · simp [stopBefore, hh, run, Function.comp_def, PMF.map]
      · have hf : hit request = false := Bool.eq_false_iff.mpr hh
        simp only [stopBefore, hf, Bool.false_eq_true, ↓reduceIte, run, PMF.map_bind,
          PMF.map_comp, Function.comp_def, List.any_cons, Bool.false_or]
        congr 1
        funext answer
        exact ih answer.2 answer.1

/-- The subtype makes the exclusion of marked requests part of the syntax. -/
def stopBeforeAllowed (hit : Request → Bool) : Program Request Response Result →
    Program {request // hit request = false} Response Bool
  | .done _ => .done false
  | .query request next => if h : hit request = false then
      .query ⟨request, h⟩ (fun response => stopBeforeAllowed hit (next response))
      else .done true
  | .coin next => .coin (fun bit => stopBeforeAllowed hit (next bit))

theorem stopBeforeAllowed_val (hit : Request → Bool)
    (program : Program Request Response Result) :
    (stopBeforeAllowed hit program).mapQueries Subtype.val id = stopBefore hit program := by
  induction program with
  | done result => rfl
  | coin next ih => simp [stopBeforeAllowed, stopBefore, mapQueries, ih]
  | query request next ih =>
      cases hh : hit request <;> simp [stopBeforeAllowed, stopBefore, hh, mapQueries, ih]

/-- Execute at most `queries` calls, then return the next request without
issuing it. Local coins needed to select that request are still executed.
A finished computation returns none. No hidden-state predicate is inspected. -/
def queryPrefix (queries : Nat) : Program Request Response Result → Program Request Response (Option Request)
  | .done _ => .done none
  | .query request next => match queries with
    | 0 => .done (some request)
    | queries + 1 => .query request (fun response => queryPrefix queries (next response))
  | .coin next => .coin (fun bit => queryPrefix queries (next bit))

/-- Prefix extraction never makes more than its specified number of calls,
regardless of the original computation's query budget. -/
theorem queryPrefix_queries (queries : Nat) (program : Program Request Response Result) :
    (queryPrefix queries program).BoundedQueries queries := by
  induction program generalizing queries with
  | done result => exact .done _ _
  | coin next ih => exact .coin _ _ (fun bit => ih bit queries)
  | query request next ih =>
      cases queries with
      | zero => exact .done _ _
      | succ queries => exact .query _ _ queries (fun response => ih response queries)

/-- The stopped transcript and selected next request are exactly the prefix
and next request of the original complete interaction in distribution.
The post-prefix hidden state is retained by execution, not reconstructed from
the final hidden state of the complete interaction. -/
theorem queryPrefix_trace (queries : Nat) (program : Program Request Response Result)
    (oracle : Oracle Request Response State) (state : State) :
    ((queryPrefix queries program).run oracle state).map (fun out => (out.trace, out.result)) =
      (program.run oracle state).map (fun out =>
        (out.trace.take queries, (out.trace[queries]?).map Prod.fst)) := by
  induction program generalizing queries state with
  | done result => simp [queryPrefix, run, PMF.pure_map]
  | coin next ih =>
      simp only [queryPrefix, run, PMF.map_bind]
      congr 1
      funext bit
      exact ih bit queries state
  | query request next ih =>
      cases queries with
      | zero => simp [queryPrefix, run, Function.comp_def, PMF.map]
      | succ queries =>
          simp only [queryPrefix, run, PMF.map_bind, PMF.map_comp, Function.comp_def,
            List.take_succ_cons, List.getElem?_cons_succ]
          congr 1
          funext answer
          have h := congrArg (PMF.map (fun pair => ((request, answer.2) :: pair.1, pair.2)))
            (ih answer.2 queries answer.1)
          simpa only [PMF.map_comp, Function.comp_def] using h

end CryptoOracle.Program
