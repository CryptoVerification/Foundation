import Foundation.Crypto.Semantics.ProcedureStoppedIteration
import Foundation.Crypto.Semantics.BoundaryReachability
import Foundation.Crypto.Semantics.Oracle.OneUseSource

/-! Stop actual adaptive execution at its first successful acceptance.
Invalid requests continue normally and retain the unused key. Exhausting
the horizon does not count as acceptance. The native computation and the
caller after acceptance belong to the unchanged residual execution. -/
namespace CryptoOracle.Interactive.FirstAcceptance
open Foundation.Probability TimedExecution
universe u
variable {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)

noncomputable def execution (fuel : Nat) :=
  Procedure.stepsUntil (OneUseSource.step native code oracle) OneUseSource.used fuel

theorem costed (fuel : Nat) (start : OneUseSource.Control State) :
    (execution native code oracle fuel).costed start =
      runToBoundary (OneUseSource.step native code oracle) OneUseSource.used fuel start :=
  Procedure.stepsUntil_costed _ _ _ _

theorem budget (fuel : Nat) (start : OneUseSource.Control State) :
    (execution native code oracle fuel).budget start = fuel := by
  unfold execution Procedure.stepsUntil
  rw [Procedure.until_budget, Nat.mul_one]

theorem reached_or_exhausted (fuel : Nat) (start : OneUseSource.Control State)
    (result : OneUseSource.Control State × Nat)
    (h : result ∈ ((execution native code oracle fuel).costed start).support) :
    OneUseSource.used result.1 = true ∨ result.2 = fuel := by
  rw [costed] at h
  exact boundary_or_exhausted _ _ _ _ _ h

theorem reachable (fuel : Nat) (start : OneUseSource.Control State)
    (result : OneUseSource.Control State × Nat)
    (h : result ∈ ((execution native code oracle fuel).costed start).support) :
    result.1 ∈ (TimedExecution.eval (OneUseSource.step native code oracle) result.2 start).support := by
  rw [costed] at h
  exact runToBoundary_reachable _ _ _ _ _ h

theorem acceptance_witness (fuel : Nat) (start : OneUseSource.Control State)
    (result : OneUseSource.Control State × Nat) (hUnused : OneUseSource.used start = false)
    (hUsed : OneUseSource.used result.1 = true)
    (h : result ∈ ((execution native code oracle fuel).costed start).support) :
    ∃ before, before ∈ (TimedExecution.eval (OneUseSource.step native code oracle) (result.2 - 1) start).support ∧
      OneUseSource.used before = false ∧ OneUseSource.accepted before = true ∧
      result.1 ∈ (OneUseSource.step native code oracle before).support := by
  rw [costed] at h
  obtain ⟨before, hr, hb, hl⟩ := runToBoundary_last_step _ _ _ _ _ hUnused hUsed h
  have hs := OneUseSource.status native code oracle before result.1 hl
  rw [hb, Bool.false_or, hUsed] at hs
  exact ⟨before, hr, hb, hs.symm, hl⟩

/-- A proof that all branches eventually used the key certifies successful
first arrival. This obligation is not inferred from a supplied fuel value. -/
theorem completes (fuel : Nat) (start : OneUseSource.Control State)
    (hComplete : ∀ finish ∈ (TimedExecution.eval (OneUseSource.step native code oracle) fuel start).support,
      OneUseSource.used finish = true)
    (result : OneUseSource.Control State × Nat)
    (h : result ∈ ((execution native code oracle fuel).costed start).support) :
    OneUseSource.used result.1 = true := by
  rw [costed] at h
  exact runToBoundary_completes _ _ _ _ hComplete _ h

/-- The remaining budget executes the original machine, starting at the
real accepted state, including its private tapes and pending native code. -/
theorem resume_law (fuel horizon : Nat) (hFuel : fuel ≤ horizon)
    (start : OneUseSource.Control State) :
    TimedExecution.eval (OneUseSource.step native code oracle) horizon start =
      ((execution native code oracle fuel).costed start).bind
        (fun result => TimedExecution.eval (OneUseSource.step native code oracle)
          (horizon - result.2) result.1) := by
  rw [costed]
  exact runToBoundary_law _ _ _ _ _ hFuel

theorem exhausted_when_unused (fuel : Nat) (start : OneUseSource.Control State)
    (hUnused : ∀ finish ∈ (TimedExecution.eval (OneUseSource.step native code oracle) fuel start).support,
      OneUseSource.used finish = false)
    (result : OneUseSource.Control State × Nat)
    (h : result ∈ ((execution native code oracle fuel).costed start).support) :
    OneUseSource.used result.1 = false ∧ result.2 = fuel := by
  have hu : OneUseSource.used result.1 = false := by
    cases hb : OneUseSource.used result.1 with
    | false => rfl
    | true =>
        obtain ⟨finish, hFinish⟩ := (TimedExecution.eval (OneUseSource.step native code oracle)
          (fuel - result.2) result.1).support_nonempty
        have hm : finish ∈ (TimedExecution.eval (OneUseSource.step native code oracle) fuel start).support := by
          rw [resume_law native code oracle fuel fuel (Nat.le_refl _), PMF.mem_support_bind_iff]
          exact ⟨result, h, hFinish⟩
        have ht := OneUseSource.spent_preserved native code oracle (fuel - result.2) result.1 finish hb hFinish
        have hf := hUnused finish hm
        simp [ht] at hf
  refine ⟨hu, ?_⟩
  rcases reached_or_exhausted native code oracle fuel start result h with hr | he
  · simp [hu] at hr
  · exact he

end CryptoOracle.Interactive.FirstAcceptance
