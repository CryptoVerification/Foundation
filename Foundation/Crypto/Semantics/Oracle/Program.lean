import Foundation.Crypto.Semantics.Probability.Comp

/-! Explicit adaptive oracle computations. Oracle calls are syntax nodes,
not unrestricted host function calls. Local fair coins are separate nodes.
The interpreter retains oracle state and records each request and response.
This semantics counts queries; it does not assign CPU costs to host continuations. -/

namespace CryptoOracle

open Foundation.Probability

universe u v w s

inductive Program (Request : Type u) (Response : Type v) (Result : Type w) where
  | done : Result → Program Request Response Result
  | query : Request → (Response → Program Request Response Result) →
      Program Request Response Result
  | coin : (Bool → Program Request Response Result) → Program Request Response Result

structure Outcome (Request : Type u) (Response : Type v)
    (Result : Type w) (State : Type s) where
  result : Result
  state : State
  trace : List (Request × Response)

abbrev Oracle (Request : Type u) (Response : Type v) (State : Type s) :=
  State → Request → ProbComp (State × Response)

namespace Program

variable {Request : Type u} {Response : Type v} {Result : Type w} {State : Type s}

noncomputable def run (oracle : Oracle Request Response State) (state : State) :
    Program Request Response Result → ProbComp (Outcome Request Response Result State)
  | .done result => PMF.pure ⟨result, state, []⟩
  | .query request next =>
      (oracle state request).bind fun response =>
        (run oracle response.1 (next response.2)).map fun outcome =>
          { outcome with trace := (request, response.2) :: outcome.trace }
  | .coin next => sampleBit.bind fun bit => run oracle state (next bit)

/-- Worst-case query bound over every response and local coin choice.
It is independent of the particular oracle used in a security game. -/
inductive BoundedQueries : Program Request Response Result → Nat → Prop where
  | done (result : Result) (q : Nat) : BoundedQueries (.done result) q
  | query (request : Request) (next : Response → Program Request Response Result)
      (q : Nat) (h : ∀ response, BoundedQueries (next response) q) :
      BoundedQueries (.query request next) (q + 1)
  | coin (next : Bool → Program Request Response Result) (q : Nat)
      (h : ∀ bit, BoundedQueries (next bit) q) : BoundedQueries (.coin next) q

theorem BoundedQueries.mono {p : Program Request Response Result} {q q' : Nat}
    (h : p.BoundedQueries q) (hqq' : q ≤ q') : p.BoundedQueries q' := by
  induction h generalizing q' with
  | done result q => exact .done result q'
  | query request next q h ih =>
      cases q' with
      | zero => omega
      | succ q' =>
          exact .query request next q' (fun response => ih response (by omega))
  | coin next q h ih => exact .coin next q' (fun bit => ih bit hqq')

/-- Every result in the experiment's support has at most the certified number
of actual oracle calls. Coin nodes do not add to the transcript. -/
theorem BoundedQueries.trace_length_le {p : Program Request Response Result} {q : Nat}
    (h : p.BoundedQueries q) (oracle : Oracle Request Response State) (state : State)
    (outcome : Outcome Request Response Result State)
    (hSupport : outcome ∈ (p.run oracle state).support) : outcome.trace.length ≤ q := by
  induction h generalizing state outcome with
  | done result q =>
      simp only [run, PMF.mem_support_pure_iff] at hSupport
      subst outcome
      exact Nat.zero_le q
  | query request next q h ih =>
      rw [run, PMF.mem_support_bind_iff] at hSupport
      obtain ⟨response, _, hMap⟩ := hSupport
      rw [PMF.mem_support_map_iff] at hMap
      obtain ⟨tail, hTail, hEq⟩ := hMap
      subst outcome
      exact Nat.succ_le_succ (ih response.2 response.1 tail hTail)
  | coin next q h ih =>
      rw [run, PMF.mem_support_bind_iff] at hSupport
      obtain ⟨bit, _, hTail⟩ := hSupport
      exact ih bit state outcome hTail

/-- Without any oracle queries, the result distribution is independent of
both the oracle and its hidden initial state. Local coins are still allowed. -/
theorem BoundedQueries.zero_run_result_eq {p : Program Request Response Result}
    (h : p.BoundedQueries 0) (left right : Oracle Request Response State)
    (leftState rightState : State) :
    (p.run left leftState).map Outcome.result =
      (p.run right rightState).map Outcome.result := by
  induction p generalizing leftState rightState with
  | done result => simp [run, PMF.pure_map]
  | query request next ih => cases h
  | coin next ih =>
      cases h with
      | coin _ _ hNext =>
          simp only [run, PMF.map_bind]
          congr 1
          funext bit
          exact ih bit (hNext bit) leftState rightState

end Program
end CryptoOracle
