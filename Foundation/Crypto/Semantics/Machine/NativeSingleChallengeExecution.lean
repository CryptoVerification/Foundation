import Foundation.Crypto.Semantics.Machine.NativeResponsePreparation
import Foundation.Crypto.Semantics.Machine.NativeEquivalentEntry

/-! Complete one-query execution for any native consumer with a public
packet entry. Response loading and control transfers are charged; the actual
padded entry is executed. Decision transport requires cell invariance only,
not normalization of the physical finite tape representation. -/
namespace Machine.NativeSingleChallenge.Execution
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {Input : Type u} {Output : Type v} {Reply : Type w}
    (distribution : PMF Reply) (raw : Reply → List Bool) (prefixBits : List Bool)
    (Q : NativeComponent Input Output) (adapt : Reply → Input)
    (hEntry : ∀ reply, Q.procedure.execution.entry (adapt reply) =
      Configuration.initial (prefixBits ++ FiniteBitEncoding.delimit (raw reply)))

noncomputable def wire : PMF (List Bool) := distribution.map raw

def executeBoundary : Control → Bool
  | .executing machine => machine.halted
  | _ => false

noncomputable def nativeInput (reply : Reply) : Q.EquivalentInput :=
  ⟨adapt reply, (NativeBitstringRewind.finish (NativeResponsePacket.rewindInput prefixBits (raw reply))).resumeAt 0,
    by rw [hEntry]; exact NativeResponsePacket.rewind_consumer_entry prefixBits (raw reply)⟩

noncomputable def consumer (reply : Reply) :
    TimedExecution.Procedure (step (wire distribution raw) Q.procedure.code) Unit Configuration :=
  (Q.equivalentEntries.reindex (fun _ : Unit => nativeInput raw prefixBits Q adapt hEntry reply)).continueIn
    (step (wire distribution raw) Q.procedure.code) executeBoundary Control.executing (fun _ => rfl)
    (fun _ _ => rfl)

noncomputable def response (reply : Reply) :
    TimedExecution.Procedure (step (wire distribution raw) Q.procedure.code) Unit Configuration :=
  (preparation (wire distribution raw) Q.procedure.code prefixBits (raw reply)).andThen
    (consumer distribution raw prefixBits Q adapt hEntry reply) (fun _ _ _ => rfl)

theorem response_entry (reply : Reply) :
    (response distribution raw prefixBits Q adapt hEntry reply).entry () =
      .seeking (Configuration.initial prefixBits) (raw reply) := by
  rw [response, TimedExecution.Procedure.andThen_entry, preparation_entry]

theorem response_exit (reply : Reply) (state : Configuration) :
    (response distribution raw prefixBits Q adapt hEntry reply).exit () state = .executing state := rfl

theorem response_budget (reply : Reply) :
    (response distribution raw prefixBits Q adapt hEntry reply).budget () =
      NativeResponsePacket.timeBound prefixBits.length (raw reply).length + Q.procedure.execution.budget (adapt reply) := by
  rw [response, TimedExecution.Procedure.andThen_budget, preparation_budget]
  rfl

theorem response_halted (reply : Reply) (state : Configuration)
    (h : state ∈ ((response distribution raw prefixBits Q adapt hEntry reply).semantics ()).support) : state.halted = true := by
  rw [response, TimedExecution.Procedure.andThen_semantics] at h
  change state ∈ ((Q.equivalentEntries.procedure.execution.semantics (nativeInput raw prefixBits Q adapt hEntry reply)).map id).support at h
  rw [PMF.map_id] at h
  exact Q.equivalentEntries.halted _ state h

/-- The logical receiver can have a fixed-width type while the actual port
stores only the raw bitstring. Encoding the reply is performed by the loader. -/
noncomputable def query : TimedExecution.Procedure (step (wire distribution raw) Q.procedure.code) Unit Reply :=
  TimedExecution.Procedure.ofFixed (step (wire distribution raw) Q.procedure.code)
    (fun _ => initial prefixBits) (fun _ reply => .seeking (Configuration.initial prefixBits) (raw reply))
    (fun _ => distribution) (fun _ => 1) (fun _ => by
      simp [eval, initial, step, wire, PMF.map_comp, Function.comp_def])

def timeBound (responseCap consumerCap : Nat) : Nat :=
  5 * prefixBits.length + 8 * responseCap + 14 + consumerCap

noncomputable def whole (responseCap consumerCap : Nat)
    (hResponse : ∀ reply ∈ distribution.support, (raw reply).length ≤ responseCap)
    (hConsumer : ∀ reply ∈ distribution.support, Q.procedure.execution.budget (adapt reply) ≤ consumerCap) :=
  (query distribution raw prefixBits Q).seq
    (TimedExecution.Procedure.family (response distribution raw prefixBits Q adapt hEntry))
    (fun _ reply _ => response_entry distribution raw prefixBits Q adapt hEntry reply)
    (fun _ => NativeResponsePacket.timeBound prefixBits.length responseCap + consumerCap) (by
      intro _ reply h
      change reply ∈ distribution.support at h
      change (response distribution raw prefixBits Q adapt hEntry reply).budget () ≤ _
      rw [response_budget]
      have hLength := hResponse reply h
      have hBudget := hConsumer reply h
      unfold NativeResponsePacket.timeBound
      omega)

variable (responseCap consumerCap : Nat)
    (hResponse : ∀ reply ∈ distribution.support, (raw reply).length ≤ responseCap)
    (hConsumer : ∀ reply ∈ distribution.support, Q.procedure.execution.budget (adapt reply) ≤ consumerCap)

theorem whole_budget :
    (whole distribution raw prefixBits Q adapt hEntry responseCap consumerCap hResponse hConsumer).budget () =
      timeBound prefixBits responseCap consumerCap := by
  change 1 + (NativeResponsePacket.timeBound prefixBits.length responseCap + consumerCap) = _
  unfold timeBound NativeResponsePacket.timeBound
  omega

theorem whole_halted (result : Reply × Configuration)
    (h : result ∈ ((whole distribution raw prefixBits Q adapt hEntry responseCap consumerCap hResponse hConsumer).semantics ()).support) :
    result.2.halted = true := by
  change result ∈ (distribution.bind (fun reply =>
    ((response distribution raw prefixBits Q adapt hEntry reply).semantics ()).map (fun state => (reply, state)))).support at h
  rw [PMF.mem_support_bind_iff] at h
  obtain ⟨reply, _, h⟩ := h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨state, hState, rfl⟩ := h
  exact response_halted distribution raw prefixBits Q adapt hEntry reply state hState

noncomputable def completion : Completion (step (wire distribution raw) Q.procedure.code) (initial prefixBits) terminal :=
  Completion.ofProcedure (whole distribution raw prefixBits Q adapt hEntry responseCap consumerCap hResponse hConsumer) rfl
    (fun result h => whole_halted distribution raw prefixBits Q adapt hEntry responseCap consumerCap hResponse hConsumer result h)

include hEntry hResponse hConsumer in
theorem run_halted (horizon : Nat)
    (hTime : timeBound prefixBits responseCap consumerCap ≤ horizon) (state : Control)
    (h : state ∈ (eval (step (wire distribution raw) Q.procedure.code) horizon (initial prefixBits)).support) :
    terminal state := by
  have hRun := (completion distribution raw prefixBits Q adapt hEntry responseCap consumerCap hResponse hConsumer).final_run
    (absorbing (wire distribution raw) Q.procedure.code) horizon (by
      change (whole distribution raw prefixBits Q adapt hEntry responseCap consumerCap hResponse hConsumer).budget () ≤ horizon
      rw [whole_budget]
      exact hTime)
  rw [hRun] at h
  exact (completion distribution raw prefixBits Q adapt hEntry responseCap consumerCap hResponse hConsumer).stopped state h

include hEntry hResponse hConsumer in
/-- Every supported execution has completed exactly one external query by
this horizon. The proof counter does not change the physical execution. -/
theorem run_exactly_one_query (horizon : Nat)
    (hTime : timeBound prefixBits responseCap consumerCap ≤ horizon) (frame : Control × Nat)
    (h : frame ∈ (eval (OneUseCounter.countedStep (step (wire distribution raw) Q.procedure.code) queryEvent)
      horizon (initial prefixBits, 0)).support) : frame.2 = 1 := by
  apply exactly_one_at_completion (wire distribution raw) Q.procedure.code prefixBits horizon frame h
  apply run_halted distribution raw prefixBits Q adapt hEntry responseCap consumerCap hResponse hConsumer horizon hTime frame.1
  rw [← OneUseCounter.marginal (step (wire distribution raw) Q.procedure.code) queryEvent horizon (initial prefixBits, 0)]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨frame, h, rfl⟩

def result (observe : Configuration → Bool) : Control → Bool
  | .executing machine => observe machine
  | _ => false

theorem response_observe (observe : Configuration → Bool)
    (invariant : ∀ first second, first.Equivalent second → observe first = observe second) (reply : Reply) :
    ((response distribution raw prefixBits Q adapt hEntry reply).semantics ()).map observe =
      (Q.procedure.execution.semantics (adapt reply)).map (fun output => observe (Q.procedure.execution.exit (adapt reply) output)) := by
  rw [response, TimedExecution.Procedure.andThen_semantics]
  change ((Q.equivalentEntries.procedure.execution.semantics (nativeInput raw prefixBits Q adapt hEntry reply)).map id).map observe = _
  rw [PMF.map_id]
  exact Q.equivalentEntries_observe _ observe invariant

include hEntry hResponse hConsumer in
/-- The complete operational game includes the query and actual response
preparation. Its distribution is the intended challenge/consumer experiment. -/
theorem run_game (observe : Configuration → Bool)
    (invariant : ∀ first second, first.Equivalent second → observe first = observe second)
    (horizon : Nat) (hTime : timeBound prefixBits responseCap consumerCap ≤ horizon) :
    (eval (step (wire distribution raw) Q.procedure.code) horizon (initial prefixBits)).map (result observe) =
      distribution.bind (fun reply => (Q.procedure.execution.semantics (adapt reply)).map
        (fun output => observe (Q.procedure.execution.exit (adapt reply) output))) := by
  have h := (completion distribution raw prefixBits Q adapt hEntry responseCap consumerCap hResponse hConsumer).final_run
    (absorbing (wire distribution raw) Q.procedure.code) horizon (by
      change (whole distribution raw prefixBits Q adapt hEntry responseCap consumerCap hResponse hConsumer).budget () ≤ horizon
      rw [whole_budget]
      exact hTime)
  rw [h]
  change ((distribution.bind (fun reply => ((response distribution raw prefixBits Q adapt hEntry reply).semantics ()).map
    (fun state => (reply, state)))).map (fun pair => Control.executing pair.2)).map (result observe) = _
  rw [PMF.map_comp, PMF.map_bind]
  congr 1
  funext reply
  rw [PMF.map_comp]
  change ((response distribution raw prefixBits Q adapt hEntry reply).semantics ()).map observe = _
  exact response_observe distribution raw prefixBits Q adapt hEntry observe invariant reply

end Machine.NativeSingleChallenge.Execution
