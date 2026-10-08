import Foundation.Crypto.Semantics.ProcedureStage
import Foundation.Crypto.Semantics.ProcedureIteration

/-! Carry proved layout and admissibility invariants through probabilistic
execution contracts. Certification adds proof data, never machine steps.
The original physical return and joint outcome/time law are preserved. -/
namespace Foundation.Probability.TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false

namespace CertifiedDistribution
variable {Value : Type u}

noncomputable def lift (distribution : PMF Value) (predicate : Value → Prop)
    (h : ∀ value ∈ distribution.support, predicate value) : PMF {value // predicate value} :=
  distribution.bindOnSupport fun value hs => PMF.pure ⟨value, h value hs⟩

theorem erase (distribution : PMF Value) (predicate : Value → Prop)
    (h : ∀ value ∈ distribution.support, predicate value) :
    (lift distribution predicate h).map Subtype.val = distribution := by
  change (distribution.bindOnSupport _).bind (PMF.pure ∘ Subtype.val) = _
  rw [← PMF.bindOnSupport_eq_bind, PMF.bindOnSupport_bindOnSupport]
  simp only [PMF.pure_bindOnSupport, Function.comp_def]
  exact PMF.bindOnSupport_pure distribution

end CertifiedDistribution
namespace Procedure
variable {State : Type u} {Input : Type v} {Output : Type w} {step : State → PMF State}

/-- Certify an output property on all supported returns, keeping the full
physical output and its correlation with the actual elapsed time. -/
noncomputable def certify (P : Procedure step Input Output) (predicate : Output → Prop)
    (h : ∀ input output, output ∈ (P.semantics input).support → predicate output) :
    Procedure step Input {output // predicate output} := by
  let outcomes : Input → PMF ({output // predicate output} × Nat) := fun input =>
    (CertifiedDistribution.lift (P.costed input) (fun result => predicate result.1)
      (fun result hs => h input result.1 (P.result_support input result hs))).map
        (fun result => (⟨result.val.1, result.property⟩, result.val.2))
  have hErase : ∀ input, (outcomes input).map (fun result => (result.1.val, result.2)) = P.costed input := by
    intro input
    simp only [outcomes, PMF.map_comp, Function.comp_def]
    exact CertifiedDistribution.erase _ _ _
  exact {
    entry := P.entry
    exit := fun input output => P.exit input output.val
    semantics := fun input => (outcomes input).map Prod.fst
    costed := outcomes
    budget := P.budget
    bounded := by
      intro input result hs
      have hOriginal : (result.1.val, result.2) ∈ (P.costed input).support := by
        rw [← hErase input, PMF.mem_support_map_iff]
        exact ⟨result, hs, rfl⟩
      exact P.bounded input (result.1.val, result.2) hOriginal
    correct := fun _ => rfl
    law := by
      intro input horizon hBudget
      rw [P.law input horizon hBudget, ← hErase input, PMF.bind_map]
      rfl }

/-- Erasure recovers the original joint distribution, not just the marginal
output or a declared worst-case execution time. -/
theorem certify_costed (P : Procedure step Input Output) (predicate : Output → Prop)
    (h : ∀ input output, output ∈ (P.semantics input).support → predicate output) (input : Input) :
    ((P.certify predicate h).costed input).map (fun result => (result.1.val, result.2)) = P.costed input := by
  simp only [certify, PMF.map_comp, Function.comp_def]
  exact CertifiedDistribution.erase _ _ _

theorem certify_semantics (P : Procedure step Input Output) (predicate : Output → Prop)
    (h : ∀ input output, output ∈ (P.semantics input).support → predicate output) (input : Input) :
    ((P.certify predicate h).semantics input).map Subtype.val = P.semantics input := by
  rw [← (P.certify predicate h).correct, PMF.map_comp, Function.comp_def]
  have he := congrArg (fun distribution => distribution.map Prod.fst) (certify_costed P predicate h input)
  simpa only [PMF.map_comp, Function.comp_def, P.correct] using he

variable {Value : Type v}
/-- Restrict both inputs and outputs to a preserved invariant. Closure is
needed only for supported outputs of inputs that satisfy the invariant. -/
noncomputable def restrictInvariant (P : Procedure step Value Value) (predicate : Value → Prop)
    (hClosed : ∀ input, predicate input → ∀ output ∈ (P.semantics input).support, predicate output) :
    Procedure step {value // predicate value} {value // predicate value} :=
  (P.reindex Subtype.val).certify predicate (fun input => hClosed input.val input.property)

theorem restrictInvariant_semantics (P : Procedure step Value Value) (predicate : Value → Prop)
    (hClosed : ∀ input, predicate input → ∀ output ∈ (P.semantics input).support, predicate output)
    (input : {value // predicate value}) :
    ((P.restrictInvariant predicate hClosed).semantics input).map Subtype.val = P.semantics input.val :=
  certify_semantics _ _ _ input

variable (P : Procedure step Value Value) (predicate : Value → Prop)
    (hClosed : ∀ input, predicate input → ∀ output ∈ (P.semantics input).support, predicate output)
    (bound : Nat) (hBound : ∀ input, predicate input → P.budget input ≤ bound)
    (hReturn : ∀ input, predicate input → ∀ output ∈ (P.semantics input).support,
      P.exit input output = P.entry output)

include hReturn in
theorem restrictInvariant_return (input output : {value // predicate value})
    (h : output ∈ ((P.restrictInvariant predicate hClosed).semantics input).support) :
    (P.restrictInvariant predicate hClosed).exit input output =
      (P.restrictInvariant predicate hClosed).entry output := by
  apply hReturn input.val input.property output.val
  rw [← restrictInvariant_semantics P predicate hClosed input, PMF.mem_support_map_iff]
  exact ⟨output, h, rfl⟩

/-- Repeat only certified states; invariant proofs do not become runtime
code, and budgets need hold only on admissible inputs. -/
noncomputable def invariantIteration (count : Nat) :=
  (P.restrictInvariant predicate hClosed).iterate bound
    (fun input => hBound input.val input.property)
    (restrictInvariant_return P predicate hClosed hReturn) count

theorem invariantIteration_semantics (count : Nat) (input : {value // predicate value}) :
    ((invariantIteration P predicate hClosed bound hBound hReturn count).semantics input).map Subtype.val =
      eval P.semantics count input.val := by
  induction count generalizing input with
  | zero => simp [invariantIteration, iterate_semantics_zero, eval, PMF.pure_map]
  | succ count ih =>
      unfold invariantIteration
      rw [iterate_semantics_succ, PMF.map_bind]
      change ((P.restrictInvariant predicate hClosed).semantics input).bind
        (fun output => ((invariantIteration P predicate hClosed bound hBound hReturn count).semantics output).map Subtype.val) = _
      simp only [ih]
      change ((P.restrictInvariant predicate hClosed).semantics input).bind
        (eval P.semantics count ∘ Subtype.val) = _
      rw [← PMF.bind_map, restrictInvariant_semantics]
      rfl

include hClosed hBound hReturn in
/-- The actual target completes only if every supported logical final state
is physically absorbing. Invariant preservation alone proves no stopping. -/
theorem invariantIteration_final (count : Nat) (input : {value // predicate value})
    (hFinal : ∀ final ∈ (eval P.semantics count input.val).support,
      step (P.entry final) = PMF.pure (P.entry final))
    (horizon : Nat) (hBudget : count * bound ≤ horizon) :
    eval step horizon (P.entry input.val) = (eval P.semantics count input.val).map P.entry := by
  let restricted := P.restrictInvariant predicate hClosed
  let all := invariantIteration P predicate hClosed bound hBound hReturn count
  have hSem := invariantIteration_semantics P predicate hClosed bound hBound hReturn count input
  have hRun := all.final_run input (fun output hOutput => by
    change step ((restricted.iterate bound _ _ count).exit input output) =
      PMF.pure ((restricted.iterate bound _ _ count).exit input output)
    rw [iterate_exit]
    change step (P.entry output.val) = PMF.pure (P.entry output.val)
    apply hFinal output.val
    rw [← hSem, PMF.mem_support_map_iff]
    exact ⟨output, hOutput, rfl⟩) horizon (by
      change (restricted.iterate bound _ _ count).budget input ≤ horizon
      rw [iterate_budget]
      exact hBudget)
  change eval step horizon ((restricted.iterate bound _ _ count).entry input) = _ at hRun
  rw [iterate_entry] at hRun
  change eval step horizon (P.entry input.val) = (all.semantics input).map (all.exit input) at hRun
  rw [hRun]
  change (all.semantics input).map (fun output => (restricted.iterate bound _ _ count).exit input output) = _
  simp only [iterate_exit]
  rw [← hSem, PMF.map_comp]
  rfl

end Procedure
end Foundation.Probability.TimedExecution
