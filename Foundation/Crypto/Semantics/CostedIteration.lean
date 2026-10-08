import Foundation.Crypto.Semantics.ProcedureStoppedIteration

/-! Exact cost-preserving public simulations of repeated execution blocks.
Each round receives the previous result, so future choices may be adaptive.
These are analyses of existing contracts, not new free machine operations. -/
namespace Foundation.Probability.CostedIteration
universe u v
variable {Source : Type u} {Target : Type v}

noncomputable def eval (kernel : Source → PMF (Source × Nat)) : Nat → Source → PMF (Source × Nat)
  | 0, start => PMF.pure (start, 0)
  | rounds + 1, start => (kernel start).bind fun first =>
      (eval kernel rounds first.1).map (fun second => (second.1, first.2 + second.2))

def project (view : Source → Target) (result : Source × Nat) : Target × Nat :=
  (view result.1, result.2)

/-- Preserve the joint distribution of the public state and accumulated
actual cost. A marginal equality for the state alone is insufficient. -/
theorem eval_map (source : Source → PMF (Source × Nat)) (target : Target → PMF (Target × Nat))
    (view : Source → Target)
    (hRound : ∀ start, (source start).map (project view) = target (view start))
    (rounds : Nat) (start : Source) :
    (eval source rounds start).map (project view) = eval target rounds (view start) := by
  induction rounds generalizing start with
  | zero => simp [eval, project, PMF.pure_map]
  | succ rounds ih =>
      rw [eval, eval, ← hRound start]
      simp only [PMF.map_bind, PMF.bind_map, Function.comp_def, PMF.map_comp, project]
      congr 1
      funext first
      have h := congrArg (fun distribution => distribution.map
        (fun second => (second.1, first.2 + second.2))) (ih first.1)
      simpa only [PMF.map_comp, Function.comp_def, project] using h

noncomputable def guarded (kernel : Source → PMF (Source × Nat)) (stop : Source → Bool)
    (start : Source) : PMF (Source × Nat) :=
  if stop start then PMF.pure (start, 0) else kernel start

theorem guarded_map (source : Source → PMF (Source × Nat)) (target : Target → PMF (Target × Nat))
    (view : Source → Target) (sourceStop : Source → Bool) (targetStop : Target → Bool)
    (hStop : ∀ start, sourceStop start = targetStop (view start))
    (hRound : ∀ start, (source start).map (project view) = target (view start))
    (start : Source) :
    (guarded source sourceStop start).map (project view) = guarded target targetStop (view start) := by
  unfold guarded
  rw [hStop]
  cases hs : targetStop (view start) <;> simp [project, PMF.pure_map, hRound]

theorem guarded_eval_map (source : Source → PMF (Source × Nat)) (target : Target → PMF (Target × Nat))
    (view : Source → Target) (sourceStop : Source → Bool) (targetStop : Target → Bool)
    (hStop : ∀ start, sourceStop start = targetStop (view start))
    (hRound : ∀ start, (source start).map (project view) = target (view start))
    (rounds : Nat) (start : Source) :
    (eval (guarded source sourceStop) rounds start).map (project view) =
      eval (guarded target targetStop) rounds (view start) :=
  eval_map _ _ view (guarded_map source target view sourceStop targetStop hStop hRound) rounds start

end Foundation.Probability.CostedIteration

namespace Foundation.Probability.TimedExecution.Procedure
universe u v w
variable {State : Type u} {Value : Type v} {Public : Type w} {step : State → PMF State}
    (P : Procedure step Value Value) (bound : Nat)
    (hBound : ∀ input, P.budget input ≤ bound)
    (hReturn : ∀ input output, output ∈ (P.semantics input).support → P.exit input output = P.entry output)

theorem iterate_costed_eval (rounds : Nat) (input : Value) :
    (P.iterate bound hBound hReturn rounds).costed input = CostedIteration.eval P.costed rounds input := by
  induction rounds generalizing input with
  | zero => simp [iterate, iteration, Procedure.ofFixed, PMF.pure_map, CostedIteration.eval]
  | succ rounds ih =>
      rw [iterate_costed_succ, CostedIteration.eval]
      congr 1
      funext first
      rw [ih]

theorem iterate_public_cost (publicKernel : Public → PMF (Public × Nat)) (view : Value → Public)
    (hRound : ∀ input, (P.costed input).map (CostedIteration.project view) = publicKernel (view input))
    (rounds : Nat) (input : Value) :
    ((P.iterate bound hBound hReturn rounds).costed input).map (CostedIteration.project view) =
      CostedIteration.eval publicKernel rounds (view input) := by
  rw [iterate_costed_eval]
  exact CostedIteration.eval_map _ _ _ hRound rounds input

theorem iterateUntil_public_cost (stop : Value → Bool) (publicStop : Public → Bool)
    (publicKernel : Public → PMF (Public × Nat)) (view : Value → Public)
    (hStop : ∀ input, stop input = publicStop (view input))
    (hRound : ∀ input, (P.costed input).map (CostedIteration.project view) = publicKernel (view input))
    (rounds : Nat) (input : Value) :
    ((P.iterateUntil stop bound hBound hReturn rounds).costed input).map (CostedIteration.project view) =
      CostedIteration.eval (CostedIteration.guarded publicKernel publicStop) rounds (view input) := by
  unfold iterateUntil
  rw [iterate_costed_eval]
  exact CostedIteration.guarded_eval_map P.costed publicKernel view stop publicStop hStop hRound rounds input

end Foundation.Probability.TimedExecution.Procedure
