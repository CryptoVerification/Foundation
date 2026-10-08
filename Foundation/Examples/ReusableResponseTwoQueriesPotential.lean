import Foundation.Examples.ReusableResponseTwoQueriesResources
import Foundation.Crypto.Semantics.ProcedurePotential

/-! Reconstruct the whole two-query machine through invariant-indexed
adaptive composition. The remaining budget gives the existing tight bound;
contracts are supplied only for the four actual caller layouts. -/
namespace Foundation.Examples.ReusableResponseTwoQueries.Potential
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC ResponseHandoffProgram
universe u
set_option backward.isDefEq.respectTransparency false

inductive Phase where
  | first | second | finishing | stopped

def advance : Phase → Phase
  | .first => .second
  | .second => .finishing
  | .finishing => .stopped
  | .stopped => .stopped

variable {State : Type u} (oracle : BitOracle State) (key : List Bool)
    (state : State) (trace : List (List Bool × List Bool)) (request : List Bool)

def frame : Phase → Configuration State
  | .first => ⟨state, .running (caller request), trace⟩
  | .second => ⟨state, .running (afterFirst request), (request, [false]) :: trace⟩
  | .finishing => NativeCallback.resumed (afterFirst request).advance state
      ((request, [false]) :: trace) [false] [false]
  | .stopped => ⟨state, .running (finalCaller request), finalTrace trace request⟩

def embed (phase : Phase) : ReusableResponse.Control State :=
  .source (retainedKey key) (frame state trace request phase)

noncomputable def family : Phase → Procedure (ReusableResponse.step native code oracle) Unit Phase
  | .first => (first oracle key state trace request).observe (fun _ => .second)
      (fun _ output => embed key state trace request output)
      (by intro _ output _; rcases output with ⟨⟨⟩, ⟨⟩⟩; rfl)
  | .second => (second oracle key state trace request).observe (fun _ => .finishing)
      (fun _ output => embed key state trace request output)
      (by intro _ output _; rcases output with ⟨⟨⟩, ⟨⟩⟩; rfl)
  | .finishing => (finish oracle key state trace request).observe (fun _ => .stopped)
      (fun _ output => embed key state trace request output)
      (by intro _ output _; cases output; rfl)
  | .stopped => Procedure.ofFixed (ReusableResponse.step native code oracle)
      (fun _ => embed key state trace request .stopped)
      (fun _ output => embed key state trace request output)
      (fun _ => PMF.pure .stopped) (fun _ => 0)
      (fun _ => by simp [TimedExecution.eval, PMF.pure_map])

theorem family_entry (phase : Phase) :
    (family oracle key state trace request phase).entry () = embed key state trace request phase := by
  cases phase <;> rfl

theorem family_exit (phase output : Phase) :
    (family oracle key state trace request phase).exit () output = embed key state trace request output := by
  cases phase <;> rfl

theorem family_semantics (phase : Phase) :
    (family oracle key state trace request phase).semantics () = PMF.pure (advance phase) := by
  cases phase <;>
    simp [family, advance, first, second, query, capture, finish, Procedure.observe, Procedure.seq,
      TimedExecution.Procedure.ofFixed, body_semantics_all, PMF.pure_map]

def stageBudget : Phase → Nat
  | .first => 9 * key.length + 5 * request.length + 30
  | .second => 9 * key.length + 35
  | .finishing => 1
  | .stopped => 0

theorem family_budget (phase : Phase) :
    (family oracle key state trace request phase).budget () = stageBudget key request phase := by
  cases phase with
  | first => change (first oracle key state trace request).budget () = _; rw [first, query_budget]; rfl
  | second => change (second oracle key state trace request).budget () = _; rw [second, query_budget]; simp [stageBudget]
  | finishing => rfl
  | stopped => rfl

def remaining : Phase → Nat
  | .first => 18 * key.length + 5 * request.length + 66
  | .second => 9 * key.length + 36
  | .finishing => 1
  | .stopped => 0

theorem consumes (phase : Phase) (result : Phase × Nat)
    (h : result ∈ ((family oracle key state trace request phase).costed ()).support) :
    (family oracle key state trace request phase).budget () + remaining key request result.1 ≤
      remaining key request phase := by
  have hs := (family oracle key state trace request phase).result_support () result h
  rw [family_semantics, PMF.mem_support_pure_iff] at hs
  rw [family_budget, hs]
  cases phase <;> simp only [stageBudget, remaining, advance] <;> omega

noncomputable def whole :=
  Stage.Potential.whole (embed key state trace request) (family oracle key state trace request)
    (family_entry oracle key state trace request) (family_exit oracle key state trace request)
    (remaining key request) (consumes oracle key state trace request) 3

theorem budget (phase : Phase) :
    (whole oracle key state trace request).budget phase = remaining key request phase :=
  Stage.Potential.whole_budget _ _ _ _ _ _ 3 phase

theorem completed :
    TimedExecution.eval (fun phase => (family oracle key state trace request phase).semantics ()) 3 .first =
      PMF.pure .stopped := by
  simp [TimedExecution.eval, family_semantics, advance, PMF.pure_bind]

theorem whole_semantics :
    (whole oracle key state trace request).semantics .first = PMF.pure .stopped := by
  rw [whole, Stage.Potential.whole_semantics]
  exact completed oracle key state trace request

theorem run (horizon : Nat) (hBudget : 18 * key.length + 5 * request.length + 66 ≤ horizon) :
    TimedExecution.eval (ReusableResponse.step native code oracle) horizon
      (.source (retainedKey key) ⟨state, .running (caller request), trace⟩) =
      PMF.pure (.source (retainedKey key) ⟨state, .running (finalCaller request), finalTrace trace request⟩) := by
  have h := Stage.Potential.whole_run (embed key state trace request) (family oracle key state trace request)
    (family_entry oracle key state trace request) (family_exit oracle key state trace request)
    (remaining key request) (consumes oracle key state trace request) 3 .first
    (by
      intro final hf
      rw [completed, PMF.mem_support_pure_iff] at hf
      subst final
      simp [embed, frame, ReusableResponse.step, ReusableResponseSource.step, Reification.timedStep,
        Reification.terminal, finalCaller, PMF.pure_map]) horizon hBudget
  rw [completed, PMF.pure_map] at h
  exact h

end Foundation.Examples.ReusableResponseTwoQueries.Potential
