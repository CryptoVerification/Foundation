import Foundation.Crypto.Semantics.KeyedContinuation

/-! Security composition with actual initialization time. The conditional
key distributions are supplied with an exact joint-distribution certificate;
no independence of the generated key and generation time is assumed. -/
namespace Foundation.Probability.InitializedContinuation
universe u v
variable {Key : Type u} {Observed : Type v}

noncomputable def compose (generated : PMF (Key × Nat))
    (suffix : Key → PMF (Observed × Nat)) : PMF (Observed × Nat) :=
  generated.bind fun first => (suffix first.1).map fun second =>
    (second.1, first.2 + second.2)

/-- Average using the key distribution conditional on each generation time.
Both initialization and continuation costs remain in the public result. -/
theorem compose_by_time (generated : PMF (Key × Nat))
    (suffix : Key → PMF (Observed × Nat)) (times : PMF Nat)
    (keysAt : Nat → PMF Key) (commonSuffix : Nat → PMF (Observed × Nat))
    (hGenerated : generated = times.bind (fun time => (keysAt time).map (fun key => (key, time))))
    (hSuffix : ∀ time, (keysAt time).bind suffix = commonSuffix time) :
    compose generated suffix = times.bind (fun time =>
      (commonSuffix time).map (fun result => (result.1, time + result.2))) := by
  unfold compose
  rw [hGenerated, PMF.bind_bind]
  congr 1
  funext time
  rw [PMF.bind_map]
  have h := congrArg (fun distribution => distribution.map
    (fun result => (result.1, time + result.2))) (hSuffix time)
  simpa only [PMF.map_bind, Function.comp_def] using h

/-- Timing-conditioned security suffices even when timing changes the key
distribution. Equality under the unconditional key marginal is not required. -/
theorem compose_eq (generated : PMF (Key × Nat))
    (left right : Key → PMF (Observed × Nat)) (times : PMF Nat)
    (keysAt : Nat → PMF Key)
    (hGenerated : generated = times.bind (fun time => (keysAt time).map (fun key => (key, time))))
    (hSuffix : ∀ time, (keysAt time).bind left = (keysAt time).bind right) :
    compose generated left = compose generated right := by
  rw [compose_by_time generated left times keysAt
    (fun time => (keysAt time).bind left) hGenerated (fun _ => rfl)]
  rw [compose_by_time generated right times keysAt
    (fun time => (keysAt time).bind left) hGenerated (fun time => (hSuffix time).symm)]

/-- Independent generation time is a sufficient special case. -/
theorem compose_independent (keys : PMF Key) (times : PMF Nat)
    (suffix : Key → PMF (Observed × Nat)) (commonSuffix : PMF (Observed × Nat))
    (hSuffix : keys.bind suffix = commonSuffix) :
    compose (times.bind (fun time => keys.map (fun key => (key, time)))) suffix =
      times.bind (fun time => commonSuffix.map (fun result => (result.1, time + result.2))) :=
  compose_by_time _ suffix times (fun _ => keys) (fun _ => commonSuffix) rfl (fun _ => hSuffix)

end Foundation.Probability.InitializedContinuation

namespace Foundation.Probability.TimedExecution.Procedure
universe u v w x y z
variable {State : Type u} {Input : Type v} {Key : Type w} {Output : Type x}
    {Observed : Type y} {step : State → PMF State}

/-- Scheme-independent security composition for actual executable contracts.
The initialization exit must be the consumer entry; no free store rebuild is
performed. Conditional key distributions certify possible timing leakage. -/
theorem initialized_seq_public_cost
    (init : Procedure step Input Key) (continuation : Procedure step Key Output)
    (handoff : ∀ input key, key ∈ (init.semantics input).support →
      continuation.entry key = init.exit input key)
    (cap : Input → Nat)
    (hCap : ∀ input key, key ∈ (init.semantics input).support →
      continuation.budget key ≤ cap input)
    (input : Input) (times : PMF Nat) (keysAt : Nat → PMF Key)
    (hGenerated : init.costed input =
      times.bind (fun time => (keysAt time).map (fun key => (key, time))))
    (view : Key → Output → Observed) (commonSuffix : Nat → PMF (Observed × Nat))
    (hSuffix : ∀ time, (keysAt time).bind (fun key => (continuation.costed key).map
      (fun result => (view key result.1, result.2))) = commonSuffix time) :
    ((init.seq continuation handoff cap hCap).costed input).map
      (fun result => (view result.1.1 result.1.2, result.2)) =
      times.bind (fun time => (commonSuffix time).map
        (fun result => (result.1, time + result.2))) := by
  have h := InitializedContinuation.compose_by_time (init.costed input)
    (fun key => (continuation.costed key).map (fun result => (view key result.1, result.2)))
    times keysAt commonSuffix hGenerated hSuffix
  simpa only [Procedure.seq, InitializedContinuation.compose, PMF.map_bind,
    PMF.map_comp, Function.comp_def] using h

/-- Two physically verified experiments may have different initialization
and continuation programs. Their public result/total-time laws agree when
their generated key/time laws and timing-conditioned suffix laws agree. -/
theorem initialized_seq_public_cost_eq
    {RightState : Type z} {RightOutput : Type x} {rightStep : RightState → PMF RightState}
    (leftInit : Procedure step Input Key) (rightInit : Procedure rightStep Input Key)
    (left : Procedure step Key Output) (right : Procedure rightStep Key RightOutput)
    (leftHandoff : ∀ input key, key ∈ (leftInit.semantics input).support →
      left.entry key = leftInit.exit input key)
    (rightHandoff : ∀ input key, key ∈ (rightInit.semantics input).support →
      right.entry key = rightInit.exit input key)
    (leftCap rightCap : Input → Nat)
    (hLeftCap : ∀ input key, key ∈ (leftInit.semantics input).support → left.budget key ≤ leftCap input)
    (hRightCap : ∀ input key, key ∈ (rightInit.semantics input).support → right.budget key ≤ rightCap input)
    (input : Input) (times : PMF Nat) (keysAt : Nat → PMF Key)
    (hLeftGenerated : leftInit.costed input =
      times.bind (fun time => (keysAt time).map (fun key => (key, time))))
    (hRightGenerated : rightInit.costed input =
      times.bind (fun time => (keysAt time).map (fun key => (key, time))))
    (leftView : Key → Output → Observed) (rightView : Key → RightOutput → Observed)
    (hSuffix : ∀ time,
      (keysAt time).bind (fun key => (left.costed key).map (fun result => (leftView key result.1, result.2))) =
      (keysAt time).bind (fun key => (right.costed key).map (fun result => (rightView key result.1, result.2)))) :
    ((leftInit.seq left leftHandoff leftCap hLeftCap).costed input).map
      (fun result => (leftView result.1.1 result.1.2, result.2)) =
    ((rightInit.seq right rightHandoff rightCap hRightCap).costed input).map
      (fun result => (rightView result.1.1 result.1.2, result.2)) := by
  rw [initialized_seq_public_cost leftInit left leftHandoff leftCap hLeftCap input times keysAt
    hLeftGenerated leftView
    (fun time => (keysAt time).bind (fun key => (left.costed key).map (fun result => (leftView key result.1, result.2))))
    (fun _ => rfl)]
  rw [initialized_seq_public_cost rightInit right rightHandoff rightCap hRightCap input times keysAt
    hRightGenerated rightView
    (fun time => (keysAt time).bind (fun key => (left.costed key).map (fun result => (leftView key result.1, result.2))))
    (fun time => (hSuffix time).symm)]

end Foundation.Probability.TimedExecution.Procedure
