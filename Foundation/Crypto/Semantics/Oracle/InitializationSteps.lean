import Foundation.Crypto.Semantics.Oracle.OneUseSteps
import Foundation.Crypto.Semantics.Oracle.OneUseInitialization

/-! Request and acceptance counts cover private key generation as well as
all subsequent adaptive controller phases. The counters are ghost state. -/
namespace CryptoOracle.Interactive.OneUseInitialization
open Foundation.Probability TimedExecution
universe u
variable {State : Type u} (generator native : Machine.Program) (code : Code)
    (oracle : BitOracle State) (caller : Configuration State)

def used : Control State → Bool
  | .initializing _ => false
  | .active source => OneUseSource.used source

def accepted : Control State → Bool
  | .initializing _ => false
  | .active source => OneUseSource.accepted source

def issued : Control State → Bool
  | .initializing _ => false
  | .active source => OneUseSource.issued code source

theorem accepted_unused (start : Control State) : accepted start = true → used start = false := by
  cases start with
  | initializing component => simp [accepted]
  | active source => exact OneUseSource.accepted_unused source

theorem status (start next : Control State)
    (h : next ∈ (step generator native code oracle caller start).support) :
    used next = (used start || accepted start) := by
  cases start with
  | initializing component =>
    cases component with
    | ready key =>
      simp only [step, PMF.mem_support_pure_iff] at h
      subst next
      rfl
    | generating machine =>
      simp only [step, PMF.mem_support_map_iff] at h
      obtain ⟨nextComponent, _, he⟩ := h
      subst next
      rfl
    | rewinding tape =>
      simp only [step, PMF.mem_support_map_iff] at h
      obtain ⟨nextComponent, _, he⟩ := h
      subst next
      rfl
  | active source =>
    simp only [step, PMF.mem_support_map_iff] at h
    obtain ⟨nextSource, hNext, he⟩ := h
    subst next
    exact OneUseSource.status native code oracle source nextSource hNext

noncomputable def execution (fuel : Nat) := Procedure.steps (step generator native code oracle caller) fuel

noncomputable def countedExecution (fuel : Nat) :=
  Procedure.steps (OneUseCounter.countedStep (step generator native code oracle caller) (issued code)) fuel

theorem counted_marginal (fuel : Nat) (start : Control State) :
    ((countedExecution generator native code oracle caller fuel).semantics (start, 0)).map Prod.fst =
      (execution generator native code oracle caller fuel).semantics start := by
  unfold countedExecution execution
  rw [Procedure.steps_semantics, Procedure.steps_semantics]
  exact OneUseCounter.marginal (step generator native code oracle caller) (issued code) fuel (start, 0)

theorem issued_bound (fuel : Nat) (start : Control State) (result : Control State × Nat)
    (h : result ∈ ((countedExecution generator native code oracle caller fuel).semantics (start, 0)).support) : result.2 ≤ fuel := by
  unfold countedExecution at h
  rw [Procedure.steps_semantics] at h
  exact EventCount.bound (step generator native code oracle caller) (issued code) fuel start result h

theorem accepted_bound (fuel : Nat) (start : Control State) (result : Control State × Nat)
    (h : result ∈ ((Procedure.steps (OneUseCounter.countedStep (step generator native code oracle caller) accepted) fuel).semantics (start, 0)).support) :
    result.2 ≤ 1 := by
  rw [Procedure.steps_semantics] at h
  exact OneUseCounter.at_most_one (step generator native code oracle caller) used accepted
    accepted_unused (status generator native code oracle caller) fuel start result h
end CryptoOracle.Interactive.OneUseInitialization
