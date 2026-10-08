import Foundation.Crypto.Semantics.Machine.NativeComponent
import Foundation.Crypto.Semantics.Machine.TapeEquivalence

/-! Reuse a native component on any cell-equivalent physical entry.
Execute the original code from the actual representation and retain its
actual full exit distribution. No tape normalization or loader is added. -/
namespace Machine.NativeComponent
open Foundation.Probability TimedExecution
universe u v
variable {Input : Type u} {Output : Type v}

structure EquivalentInput (P : NativeComponent Input Output) where
  logical : Input
  actual : Configuration
  equivalent : actual.Equivalent (P.procedure.execution.entry logical)

variable (P : NativeComponent Input Output)

theorem equivalentEntry_halted (input : EquivalentInput P) (target : Configuration)
    (hTarget : target ∈ (evalConfigWithin P.procedure.code input.actual
      (P.procedure.execution.budget input.logical)).support) : target.halted = true := by
  have hFlags := evalConfigWithin_map_eq_of_equivalent P.procedure.code _ _ input.equivalent
    (P.procedure.execution.budget input.logical) Configuration.halted (fun _ _ h => h.2.1)
  have ht : target.halted ∈ ((evalConfigWithin P.procedure.code input.actual
      (P.procedure.execution.budget input.logical)).map Configuration.halted).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨target, hTarget, rfl⟩
  rw [hFlags, P.procedure.final_run input.logical (P.halted input.logical) _ (Nat.le_refl _),
    PMF.map_comp, PMF.mem_support_map_iff] at ht
  obtain ⟨output, hOutput, hFlag⟩ := ht
  exact hFlag.symm.trans (P.halted input.logical output hOutput)

noncomputable def equivalentEntries : NativeComponent (EquivalentInput P) Configuration where
  procedure := Machine.Procedure.ofFixed P.procedure.code (fun input => input.actual)
    (fun _ output => output)
    (fun input => evalConfigWithin P.procedure.code input.actual (P.procedure.execution.budget input.logical))
    (fun input => P.procedure.execution.budget input.logical) (fun _ => (PMF.map_id _).symm)
  closed := P.closed
  entry := fun input => input.equivalent.1.trans_lt (P.entry input.logical)
  active := fun input => input.equivalent.2.1.trans (P.active input.logical)
  halted := P.equivalentEntry_halted

theorem equivalentEntries_code : P.equivalentEntries.procedure.code = P.procedure.code := rfl

theorem equivalentEntries_entry (input : EquivalentInput P) :
    P.equivalentEntries.procedure.execution.entry input = input.actual := rfl

theorem equivalentEntries_budget (input : EquivalentInput P) :
    P.equivalentEntries.procedure.execution.budget input = P.procedure.execution.budget input.logical := rfl

/-- Every observation invariant under cell equivalence has the original
distribution, including joint observations of both tapes and control. -/
theorem equivalentEntries_observe {Value : Type*} (input : EquivalentInput P)
    (observe : Configuration → Value)
    (hObserve : ∀ first second, first.Equivalent second → observe first = observe second) :
    (P.equivalentEntries.procedure.execution.semantics input).map observe =
      (P.procedure.execution.semantics input.logical).map
        (fun output => observe (P.procedure.execution.exit input.logical output)) := by
  change (evalConfigWithin P.procedure.code input.actual _).map observe = _
  rw [evalConfigWithin_map_eq_of_equivalent P.procedure.code _ _ input.equivalent _ observe hObserve,
    P.procedure.final_run input.logical (P.halted input.logical) _ (Nat.le_refl _), PMF.map_comp]
  rfl

theorem equivalentEntries_run (input : EquivalentInput P) (horizon : Nat)
    (hTime : P.procedure.execution.budget input.logical ≤ horizon) :
    evalConfigWithin P.procedure.code input.actual horizon =
      P.equivalentEntries.procedure.execution.semantics input := by
  have h := P.equivalentEntries.procedure.final_run input (P.equivalentEntries.halted input) horizon hTime
  change evalConfigWithin P.procedure.code input.actual horizon =
    (P.equivalentEntries.procedure.execution.semantics input).map id at h
  simpa only [PMF.map_id] using h

theorem equivalentEntries_postcondition (input : EquivalentInput P) (post : Configuration → Prop)
    (invariant : ∀ first second, first.Equivalent second → (post first ↔ post second))
    (source : ∀ output, output ∈ (P.procedure.execution.semantics input.logical).support →
      post (P.procedure.execution.exit input.logical output))
    (target : Configuration)
    (hTarget : target ∈ (P.equivalentEntries.procedure.execution.semantics input).support) : post target := by
  have hMap := P.equivalentEntries_observe input post (fun first second h => propext (invariant first second h))
  have ht : post target ∈ ((P.equivalentEntries.procedure.execution.semantics input).map post).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨target, hTarget, rfl⟩
  rw [hMap, PMF.mem_support_map_iff] at ht
  obtain ⟨output, hOutput, hPost⟩ := ht
  exact hPost.mp (source output hOutput)

theorem equivalentEntries_operational :
    TimedExecution.Procedure.Operational P.equivalentEntries.procedure.execution :=
  TimedExecution.Procedure.operational_ofFixed _ _ _ _ (fun (input : EquivalentInput P) =>
    (timed_eval_eq P.procedure.code input.actual _).trans (PMF.map_id _).symm)

/-- Storage uses the actual entry's cell count, which can exceed that of
the canonical representative by arbitrarily many redundant blank cells. -/
theorem equivalentEntries_storage_peak (input : EquivalentInput P) (elapsed : Nat)
    (hElapsed : elapsed ≤ P.procedure.execution.budget input.logical) (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF P.procedure.code) elapsed input.actual).support) :
    (NativeEncodedResources.completeEncoding.encode (P.procedure.code, target)).length ≤
      NativeEncodedResources.bound P.procedure.code input.actual.pc input.actual.tapeCells
        (P.procedure.execution.budget input.logical) :=
  NativeEncodedResources.peak P.procedure.code _ elapsed hElapsed _ target hTarget

theorem equivalentEntries_storage_costed (input : EquivalentInput P) (result : Configuration × Nat)
    (hResult : result ∈ (P.equivalentEntries.procedure.execution.costed input).support) :
    (NativeEncodedResources.completeEncoding.encode (P.procedure.code, result.1)).length ≤
      NativeEncodedResources.bound P.procedure.code input.actual.pc input.actual.tapeCells result.2 :=
  NativeEncodedResources.peak P.procedure.code result.2 result.2 (Nat.le_refl _) _ result.1
    (P.equivalentEntries_operational input result hResult)

end Machine.NativeComponent
