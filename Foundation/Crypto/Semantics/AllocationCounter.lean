import Foundation.Crypto.Semantics.ResourceGrowth
import Foundation.Crypto.Semantics.Simulation
import Foundation.Crypto.Semantics.Invariant

/-! An analysis counter records per-transition allocation allowances.
The physical machine and its random branches are unchanged. The counter
is not inserted into runtime code or charged as a free runtime operation. -/
namespace Foundation.Probability.TimedExecution.AllocationCounter
universe u
variable {State : Type u}

noncomputable def step (physical : State → PMF State) (charge : State → Nat)
    (current : State × Nat) : PMF (State × Nat) :=
  (physical current.1).map (fun next => (next, current.2 + charge current.1))

theorem physical_eval (physical : State → PMF State) (charge : State → Nat)
    (fuel : Nat) (start : State) (credit : Nat) :
    (eval (step physical charge) fuel (start, credit)).map Prod.fst = eval physical fuel start := by
  induction fuel generalizing start credit with
  | zero => simp [eval, PMF.pure_map]
  | succ fuel ih =>
      simp only [eval, step, PMF.map_bind, PMF.bind_map, Function.comp_def]
      congr 1
      funext next
      exact ih next (credit + charge start)

/-- Every supported history bounds its retained storage by the initial
storage plus its own accumulated allocation allowance. -/
theorem endpoint (physical : State → PMF State) (size : State → Nat) (charge : State → Nat)
    (hLocal : ∀ start next, next ∈ (physical start).support → size next ≤ size start + charge start)
    (fuel : Nat) (start : State) (result : State × Nat)
    (h : result ∈ (eval (step physical charge) fuel (start, 0)).support) :
    size result.1 ≤ size start + result.2 := by
  apply eval_preserves (step physical charge) (fun current => size current.1 ≤ size start + current.2)
    _ fuel (start, 0) result (by simp) h
  intro current hCurrent next hNext
  rw [step, PMF.mem_support_map_iff] at hNext
  obtain ⟨value, hv, he⟩ := hNext
  subst next
  have hb := hLocal current.1 value hv
  simp only at *
  omega

/-- Original machine prefixes have matching allocation certificates; the
certificate includes the real cumulative charge from that supported run. -/
theorem physical_prefix (physical : State → PMF State) (size : State → Nat) (charge : State → Nat)
    (hLocal : ∀ start next, next ∈ (physical start).support → size next ≤ size start + charge start)
    (elapsed : Nat) (start intermediate : State)
    (h : intermediate ∈ (eval physical elapsed start).support) :
    ∃ allocated, (intermediate, allocated) ∈ (eval (step physical charge) elapsed (start, 0)).support ∧
      size intermediate ≤ size start + allocated := by
  rw [← physical_eval physical charge elapsed start 0, PMF.mem_support_map_iff] at h
  obtain ⟨result, hr, he⟩ := h
  rcases result with ⟨value, allocated⟩
  change value = intermediate at he
  subst intermediate
  exact ⟨allocated, hr, endpoint physical size charge hLocal elapsed start (value, allocated) hr⟩

end Foundation.Probability.TimedExecution.AllocationCounter
