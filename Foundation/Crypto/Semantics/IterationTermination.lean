import Foundation.Crypto.Semantics.CostedIteration
import Foundation.Crypto.Semantics.ProcedureReachability

/-! Transfer a bounded stopping proof for genuine machine steps to a
costed decomposition of those steps. Every unfinished round must make real
positive progress; a zero-cost missing-layout return does not qualify. -/
namespace Foundation.Probability.TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

theorem terminal_after (step : State → PMF State) (terminal : State → Bool)
    (hAbsorb : ∀ state, terminal state = true → step state = PMF.pure state)
    (start : State) (bound : Nat)
    (hStop : ∀ state ∈ (eval step bound start).support, terminal state = true)
    (elapsed : Nat) (hElapsed : bound ≤ elapsed)
    (final : State) (hFinal : final ∈ (eval step elapsed start).support) : terminal final = true := by
  rw [show elapsed = bound + (elapsed - bound) by omega, eval_add, PMF.mem_support_bind_iff] at hFinal
  obtain ⟨middle, hm, hf⟩ := hFinal
  rw [Block.eval_of_absorbing middle (hAbsorb middle (hStop middle hm)), PMF.mem_support_pure_iff] at hf
  subst final
  exact hStop middle hm

/-- After every supported path has reached a genuine absorbing terminal,
larger horizons preserve the entire distribution, not only terminal support. -/
theorem terminal_stable (step : State → PMF State) (terminal : State → Bool)
    (hAbsorb : ∀ state, terminal state = true → step state = PMF.pure state)
    (start : State) (bound : Nat)
    (hStop : ∀ state ∈ (eval step bound start).support, terminal state = true)
    (elapsed : Nat) (hElapsed : bound ≤ elapsed) : eval step elapsed start = eval step bound start := by
  rw [show elapsed = bound + (elapsed - bound) by omega, eval_add]
  have hBind : (eval step bound start).bind (eval step (elapsed - bound)) =
      (eval step bound start).bind PMF.pure := by
    rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
    congr 1
    funext state hs
    exact Block.eval_of_absorbing state (hAbsorb state (hStop state hs)) _
  rw [hBind, PMF.bind_pure]

end Foundation.Probability.TimedExecution

namespace Foundation.Probability.CostedIteration
open TimedExecution
universe u v
variable {Value : Type u} {State : Type v}

theorem eval_marginal (kernel : Value → PMF (Value × Nat)) (rounds : Nat) (start : Value) :
    (eval kernel rounds start).map Prod.fst =
      TimedExecution.eval (fun value => (kernel value).map Prod.fst) rounds start := by
  induction rounds generalizing start with
  | zero => simp [eval, TimedExecution.eval, PMF.pure_map]
  | succ rounds ih =>
      simp only [eval, TimedExecution.eval, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]
      congr 1
      funext first
      exact ih first.1

theorem reachable (step : State → PMF State) (kernel : Value → PMF (Value × Nat))
    (embed : Value → State)
    (hRound : ∀ start result, result ∈ (kernel start).support →
      embed result.1 ∈ (TimedExecution.eval step result.2 (embed start)).support)
    (rounds : Nat) (start : Value) (result : Value × Nat)
    (hResult : result ∈ (eval kernel rounds start).support) :
    embed result.1 ∈ (TimedExecution.eval step result.2 (embed start)).support := by
  induction rounds generalizing start result with
  | zero =>
      rw [eval, PMF.mem_support_pure_iff] at hResult
      subst result
      simp [TimedExecution.eval]
  | succ rounds ih =>
      rw [eval, PMF.mem_support_bind_iff] at hResult
      obtain ⟨first, hf, hs⟩ := hResult
      rw [PMF.mem_support_map_iff] at hs
      obtain ⟨second, hs, he⟩ := hs
      subst result
      rw [TimedExecution.eval_add, PMF.mem_support_bind_iff]
      exact ⟨embed first.1, hRound start first hf, ih first.1 second hs⟩

theorem unfinished_cost (step : State → PMF State) (terminal : State → Bool)
    (hAbsorb : ∀ state, terminal state = true → step state = PMF.pure state)
    (kernel : Value → PMF (Value × Nat)) (embed : Value → State)
    (hRound : ∀ start result, result ∈ (kernel start).support →
      embed result.1 ∈ (TimedExecution.eval step result.2 (embed start)).support)
    (hProgress : ∀ start, terminal (embed start) = false →
      ∀ result ∈ (kernel start).support, 0 < result.2)
    (rounds : Nat) (start : Value) (result : Value × Nat)
    (hResult : result ∈ (eval kernel rounds start).support)
    (hUnfinished : terminal (embed result.1) = false) : rounds ≤ result.2 := by
  induction rounds generalizing start result with
  | zero => exact Nat.zero_le _
  | succ rounds ih =>
      have hStart : terminal (embed start) = false := by
        cases ht : terminal (embed start) with
        | false => rfl
        | true =>
            have hr := reachable step kernel embed hRound (rounds + 1) start result hResult
            rw [Block.eval_of_absorbing (embed start) (hAbsorb _ ht), PMF.mem_support_pure_iff] at hr
            rw [hr, ht] at hUnfinished
            contradiction
      rw [eval, PMF.mem_support_bind_iff] at hResult
      obtain ⟨first, hf, hs⟩ := hResult
      rw [PMF.mem_support_map_iff] at hs
      obtain ⟨second, hs, he⟩ := hs
      subst result
      have hp := hProgress start hStart first hf
      have hi := ih first.1 second hs hUnfinished
      omega

/-- A machine that stops by `bound` also stops after at most `bound`
positive-progress macro rounds. Their budgets need not equal their costs. -/
theorem terminal_of_steps (step : State → PMF State) (terminal : State → Bool)
    (hAbsorb : ∀ state, terminal state = true → step state = PMF.pure state)
    (kernel : Value → PMF (Value × Nat)) (embed : Value → State)
    (hRound : ∀ start result, result ∈ (kernel start).support →
      embed result.1 ∈ (TimedExecution.eval step result.2 (embed start)).support)
    (hProgress : ∀ start, terminal (embed start) = false →
      ∀ result ∈ (kernel start).support, 0 < result.2)
    (start : Value) (bound rounds : Nat) (hRounds : bound ≤ rounds)
    (hStop : ∀ state ∈ (TimedExecution.eval step bound (embed start)).support, terminal state = true)
    (final : Value)
    (hFinal : final ∈ (TimedExecution.eval (fun value => (kernel value).map Prod.fst) rounds start).support) :
    terminal (embed final) = true := by
  rw [← eval_marginal, PMF.mem_support_map_iff] at hFinal
  obtain ⟨result, hr, he⟩ := hFinal
  subst final
  cases ht : terminal (embed result.1) with
  | true => rfl
  | false =>
      have hc := unfinished_cost step terminal hAbsorb kernel embed hRound hProgress rounds start result hr ht
      have reach := reachable step kernel embed hRound rounds start result hr
      have stop := terminal_after step terminal hAbsorb (embed start) bound hStop result.2
        (hRounds.trans hc) (embed result.1) reach
      rw [ht] at stop
      contradiction

end Foundation.Probability.CostedIteration

namespace Foundation.Probability.TimedExecution.Procedure
universe u v
variable {State : Type u} {Value : Type v} {step : State → PMF State}

theorem operational_iterate (P : Procedure step Value Value) (hP : Operational P)
    (bound : Nat) (hBound : ∀ input, P.budget input ≤ bound)
    (hReturn : ∀ input output, output ∈ (P.semantics input).support → P.exit input output = P.entry output)
    (rounds : Nat) : Operational (P.iterate bound hBound hReturn rounds) := by
  intro input result hs
  rw [iterate_costed_eval] at hs
  rw [iterate_exit, iterate_entry]
  apply CostedIteration.reachable step P.costed P.entry _ rounds input result hs
  intro source returned hr
  rw [← hReturn source returned.1 (P.result_support source returned hr)]
  exact hP source returned hr

theorem operational_invariantIteration (P : Procedure step Value Value)
    (predicate : Value → Prop)
    (hClosed : ∀ input, predicate input → ∀ output ∈ (P.semantics input).support, predicate output)
    (hP : ∀ input, predicate input → ∀ result ∈ (P.costed input).support,
      P.exit input result.1 ∈ (eval step result.2 (P.entry input)).support)
    (bound : Nat) (hBound : ∀ input, predicate input → P.budget input ≤ bound)
    (hReturn : ∀ input, predicate input → ∀ output ∈ (P.semantics input).support,
      P.exit input output = P.entry output) (rounds : Nat) :
    Operational (P.invariantIteration predicate hClosed bound hBound hReturn rounds) :=
  operational_iterate (P.restrictInvariant predicate hClosed)
    (operational_restrictInvariant P predicate hClosed hP) bound
    (fun input => hBound input.val input.property)
    (restrictInvariant_return P predicate hClosed hReturn) rounds

/-- Reuse an ordinary machine stopping certificate for a composable
procedure. No stopping assumption about its logical iteration is required. -/
theorem stops_of_machine (P : Procedure step Value Value) (hP : Operational P)
    (hReturn : ∀ start result, result ∈ (P.semantics start).support → P.exit start result = P.entry result)
    (terminal : State → Bool)
    (hAbsorb : ∀ state, terminal state = true → step state = PMF.pure state)
    (hProgress : ∀ start, terminal (P.entry start) = false →
      ∀ result ∈ (P.costed start).support, 0 < result.2)
    (start : Value) (bound rounds : Nat) (hRounds : bound ≤ rounds)
    (hStop : ∀ state ∈ (eval step bound (P.entry start)).support, terminal state = true)
    (final : Value) (hFinal : final ∈ (eval P.semantics rounds start).support) :
    terminal (P.entry final) = true := by
  have hr : ∀ input result, result ∈ (P.costed input).support →
      P.entry result.1 ∈ (eval step result.2 (P.entry input)).support := by
    intro input result hs
    rw [← hReturn input result.1 (P.result_support input result hs)]
    exact hP input result hs
  apply CostedIteration.terminal_of_steps step terminal hAbsorb P.costed P.entry
    hr hProgress start bound rounds hRounds hStop final
  simpa only [P.correct] using hFinal

/-- The source-machine stop and operational progress need only hold for
admissible round entries; invalid layouts cannot be silently certified. -/
theorem invariant_stops_of_machine (P : Procedure step Value Value)
    (predicate : Value → Prop)
    (hClosed : ∀ input, predicate input → ∀ output ∈ (P.semantics input).support, predicate output)
    (hP : ∀ input, predicate input → ∀ result ∈ (P.costed input).support,
      P.exit input result.1 ∈ (eval step result.2 (P.entry input)).support)
    (hReturn : ∀ input, predicate input → ∀ output ∈ (P.semantics input).support,
      P.exit input output = P.entry output)
    (terminal : State → Bool)
    (hAbsorb : ∀ state, terminal state = true → step state = PMF.pure state)
    (hProgress : ∀ input, predicate input → terminal (P.entry input) = false →
      ∀ result ∈ (P.costed input).support, 0 < result.2)
    (start : {value // predicate value}) (bound rounds : Nat) (hRounds : bound ≤ rounds)
    (hStop : ∀ state ∈ (eval step bound (P.entry start.val)).support, terminal state = true)
    (final : Value) (hFinal : final ∈ (eval P.semantics rounds start.val).support) :
    terminal (P.entry final) = true := by
  let R := P.restrictInvariant predicate hClosed
  have hProgressR : ∀ input, terminal (R.entry input) = false →
      ∀ result ∈ (R.costed input).support, 0 < result.2 := by
    intro input ht result hs
    have ho : (result.1.val, result.2) ∈ (P.costed input.val).support := by
      change (result.1.val, result.2) ∈ ((P.reindex Subtype.val).costed input).support
      rw [← certify_costed (P.reindex Subtype.val) predicate
        (fun value => hClosed value.val value.property) input, PMF.mem_support_map_iff]
      exact ⟨result, hs, rfl⟩
    exact hProgress input.val input.property ht (result.1.val, result.2) ho
  have he := eval_map R.semantics P.semantics Subtype.val
    (restrictInvariant_semantics P predicate hClosed) rounds start
  rw [← he, PMF.mem_support_map_iff] at hFinal
  obtain ⟨certified, hc, heq⟩ := hFinal
  subst final
  exact stops_of_machine R (operational_restrictInvariant P predicate hClosed hP)
    (restrictInvariant_return P predicate hClosed hReturn) terminal hAbsorb hProgressR
    start bound rounds hRounds hStop certified hc

end Foundation.Probability.TimedExecution.Procedure
