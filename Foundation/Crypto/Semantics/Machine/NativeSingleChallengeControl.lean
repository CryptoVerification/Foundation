import Foundation.Crypto.Semantics.Machine.DelimitedResponseLoading
import Foundation.Crypto.Semantics.Machine.NativeBitstringSeekEnd
import Foundation.Crypto.Semantics.Machine.NativeBitstringRewind
import Foundation.Crypto.Semantics.OneUseCounter

/-! One external response, physically appended to the actual public input
before a fixed native consumer is called. Seeking, loading, rewinding and
all three control transfers are explicit transitions. This is an oracle
controller around native programs, not an unproved native flattening. -/
namespace Machine.NativeSingleChallenge
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

inductive Control where
  | querying : Configuration → Control
  | seeking : Configuration → List Bool → Control
  | loading : DelimitedResponseLoading.Control → Control
  | rewinding : Configuration → Control
  | executing : Configuration → Control

variable (distribution : PMF (List Bool)) (code : Program)

noncomputable def step : Control → PMF Control
  | .querying machine => distribution.map (fun response => .seeking machine response)
  | .seeking machine response =>
      if machine.halted then PMF.pure (.loading (.flag (machine.resumeAt 0) response))
      else (stepPMF NativeBitstringSeekEnd.code machine).map (fun next => .seeking next response)
  | .loading (.done machine) => PMF.pure (.rewinding (machine.resumeAt 0))
  | .loading loader => (DelimitedResponseLoading.step loader).map .loading
  | .rewinding machine =>
      if machine.halted then PMF.pure (.executing (machine.resumeAt 0))
      else (stepPMF rewindBitstring machine).map .rewinding
  | .executing machine => (stepPMF code machine).map .executing

def initial (prefixBits : List Bool) : Control := .querying (Configuration.initial prefixBits)

def terminal : Control → Prop
  | .executing machine => machine.halted = true
  | _ => False

theorem absorbing (state : Control) (h : terminal state) : step distribution code state = PMF.pure state := by
  cases state <;> simp_all [terminal, step, stepPMF, next, PMF.pure_map]

def queryEvent : Control → Bool
  | .querying _ => true
  | _ => false

def queries : Control → Nat
  | .querying _ => 0
  | _ => 1

theorem queries_le_one (state : Control) : queries state ≤ 1 := by cases state <;> simp [queries]

theorem query_step (start result : Control) (h : result ∈ (step distribution code start).support) :
    queries result = queries start + if queryEvent start then 1 else 0 := by
  cases start with
  | querying machine =>
      simp only [step, PMF.mem_support_map_iff] at h
      obtain ⟨response, _, rfl⟩ := h
      rfl
  | seeking machine response =>
      by_cases hHalt : machine.halted = true
      · simp only [step, hHalt, ↓reduceIte, PMF.mem_support_pure_iff] at h
        subst result
        rfl
      · simp only [step, hHalt, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
        obtain ⟨_, _, rfl⟩ := h
        rfl
  | loading loader =>
      cases loader <;>
        simp only [step, PMF.mem_support_map_iff, PMF.mem_support_pure_iff] at h
      all_goals first
        | (obtain ⟨_, _, rfl⟩ := h; rfl)
        | (subst result; rfl)
  | rewinding machine =>
      by_cases hHalt : machine.halted = true
      · simp only [step, hHalt, ↓reduceIte, PMF.mem_support_pure_iff] at h
        subst result
        rfl
      · simp only [step, hHalt, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
        obtain ⟨_, _, rfl⟩ := h
        rfl
  | executing machine =>
      simp only [step, PMF.mem_support_map_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      rfl

/-- The ghost counter counts actual querying transitions. It changes no
machine step and adds no runtime cost. -/
theorem query_counter (prefixBits : List Bool) (fuel : Nat) (result : Control × Nat)
    (h : result ∈ (eval (OneUseCounter.countedStep (step distribution code) queryEvent)
      fuel (initial prefixBits, 0)).support) : result.2 = queries result.1 := by
  apply eval_preserves _ (fun frame => frame.2 = queries frame.1) _ fuel (initial prefixBits, 0) result rfl h
  intro before hBefore after hAfter
  rw [OneUseCounter.countedStep, PMF.mem_support_map_iff] at hAfter
  obtain ⟨next, hNext, rfl⟩ := hAfter
  rw [query_step distribution code before.1 next hNext, hBefore]

theorem at_most_one_query (prefixBits : List Bool) (fuel : Nat) (result : Control × Nat)
    (h : result ∈ (eval (OneUseCounter.countedStep (step distribution code) queryEvent)
      fuel (initial prefixBits, 0)).support) : result.2 ≤ 1 := by
  rw [query_counter distribution code prefixBits fuel result h]
  exact queries_le_one result.1

theorem terminal_queries (state : Control) (h : terminal state) : queries state = 1 := by
  cases state <;> simp_all [terminal, queries]

/-- Every completed run has made exactly one query, rather than merely
satisfying the upper bound of one query. -/
theorem exactly_one_at_completion (prefixBits : List Bool) (fuel : Nat) (result : Control × Nat)
    (h : result ∈ (eval (OneUseCounter.countedStep (step distribution code) queryEvent)
      fuel (initial prefixBits, 0)).support) (hTerminal : terminal result.1) : result.2 = 1 :=
  (query_counter distribution code prefixBits fuel result h).trans (terminal_queries result.1 hTerminal)

theorem query_run (prefixBits : List Bool) :
    eval (step distribution code) 1 (initial prefixBits) =
      distribution.map (fun response => .seeking (Configuration.initial prefixBits) response) := by
  simp [eval, initial, step]

end Machine.NativeSingleChallenge
