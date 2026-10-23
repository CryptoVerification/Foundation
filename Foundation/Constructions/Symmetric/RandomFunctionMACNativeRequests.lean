import Foundation.Constructions.Symmetric.RandomFunctionMACNativeCorrectness
import Foundation.Crypto.Semantics.Oracle.NativeTrace

/-! Requirements at every actual oracle-call boundary of the concrete MAC
caller. Final-state refinement alone is not used as a substitute: prefix
extension and monotone actual transcripts transfer the format assertion to
every reachable awaiting state before the genuine halt.
-/
namespace Foundation.Symmetric.RandomFunctionMACNativeCaller.Native
open Foundation.Probability CryptoOracle CryptoOracle.Interactive TimedExecution
set_option backward.isDefEq.respectTransparency false

def EncodedPair (entry : List Bool × List Bool) : Prop :=
  ∃ message : Message, ∃ tag : Tag, entry = (encodeMessage message, encodeTag tag)

theorem extend_encoded (message : Message) (tag : Tag) (trace : List (List Bool × List Bool))
    (valid : ∀ entry ∈ trace, EncodedPair entry) :
    ∀ entry ∈ extendTrace message tag trace, EncodedPair entry := by
  intro entry member
  rcases List.mem_cons.mp member with same | old
  · subst entry; exact ⟨message, tag, rfl⟩
  · exact valid entry old

theorem execution_encoded {State : Type} (world : Oracle Message Tag State) (state : State)
    (trace : List (List Bool × List Bool)) (valid : ∀ entry ∈ trace, EncodedPair entry)
    (coin : Bool) (final : Configuration State) (supported : final ∈ (executionLaw world state trace coin).support) :
    ∀ entry ∈ final.reverseTrace, EncodedPair entry := by
  rw [executionLaw, PMF.mem_support_bind_iff] at supported
  obtain ⟨first, _, supported⟩ := supported
  rw [PMF.mem_support_bind_iff] at supported
  obtain ⟨second, _, supported⟩ := supported
  rw [PMF.mem_support_bind_iff] at supported
  obtain ⟨repeated, _, supported⟩ := supported
  rw [PMF.mem_support_map_iff] at supported
  obtain ⟨actual, _, rfl⟩ := supported
  exact extend_encoded 7 actual.2 _ (extend_encoded (firstMessage coin) repeated.2 _
    (extend_encoded (secondMessage first.2) second.2 _ (extend_encoded (firstMessage coin) first.2 trace valid)))

theorem prefix_encoded {State : Type} (world : Oracle Message Tag State) (state : State)
    (fuel : Nat) (within : fuel ≤ 343) (current : Configuration State)
    (supported : current ∈ (TimedExecution.eval (Reification.timedStep code (packetOracle world)) fuel
      (⟨state, .running {}, []⟩ : Configuration State)).support) :
    ∀ entry ∈ current.reverseTrace, EncodedPair entry := by
  obtain ⟨final, finalSupported, included⟩ := Reification.extend_prefix code (packetOracle world) fuel 343 within
    ⟨state, .running {}, []⟩ current supported
  rw [whole_run, PMF.mem_support_bind_iff] at finalSupported
  obtain ⟨coin, _, finalSupported⟩ := finalSupported
  intro entry member
  exact execution_encoded world state [] (by intro entry member; cases member) coin final finalSupported entry (included member)

/-- At every supported awaiting state the request is an actual encoded
three-bit message. This precondition is available before its service runs. -/
theorem awaiting_format {State : Type} (world : Oracle Message Tag State) (state : State)
    (fuel : Nat) (within : fuel ≤ 343) (current : Configuration State)
    (supported : current ∈ (TimedExecution.eval (Reification.timedStep code (packetOracle world)) fuel
      (⟨state, .running {}, []⟩ : Configuration State)).support)
    (machine : Machine.Configuration) (request : List Bool) (waiting : current.control = .awaiting machine request) :
    ∃ message : Message, request = encodeMessage message := by
  have before : fuel < 343 := by
    by_contra notBefore
    have last : fuel = 343 := by omega
    subst fuel
    have halted := (whole_halts_queries world state [] current supported).1
    simp [waiting, Reification.terminal] at halted
  obtain ⟨answer, reachable⟩ := PMF.support_nonempty (packetOracle world current.state request)
  let next : Configuration State := ⟨answer.1, .loading machine answer.2 {}, (request, answer.2) :: current.reverseTrace⟩
  have stepLaw : Reification.timedStep code (packetOracle world) current =
      (packetOracle world current.state request).map (fun response =>
        (⟨response.1, .loading machine response.2 {}, (request, response.2) :: current.reverseTrace⟩ : Configuration State)) := by
    simp [Reification.timedStep, waiting, Reification.terminal, Reification.perform, Reification.action, transition]
  have stepSupported : next ∈ (Reification.timedStep code (packetOracle world) current).support := by
    rw [stepLaw, PMF.mem_support_map_iff]
    exact ⟨answer, reachable, rfl⟩
  have nextSupported : next ∈ (TimedExecution.eval (Reification.timedStep code (packetOracle world)) (fuel + 1)
      (⟨state, .running {}, []⟩ : Configuration State)).support := by
    rw [TimedExecution.eval_add, PMF.mem_support_bind_iff]
    refine ⟨current, supported, ?_⟩
    simpa [TimedExecution.eval] using stepSupported
  obtain ⟨message, _tag, equal⟩ := prefix_encoded world state (fuel + 1) (by omega) next nextSupported
    (request, answer.2) (List.mem_cons_self ..)
  exact ⟨message, congrArg Prod.fst equal⟩

end Foundation.Symmetric.RandomFunctionMACNativeCaller.Native
