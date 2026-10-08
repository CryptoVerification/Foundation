import Foundation.Crypto.Semantics.Oracle.CountedRejection
import Foundation.Crypto.Semantics.CostedIteration

/-! Actual counted rejection rounds return to a canonical caller frame.
Finite iteration consumes the supplied marker list and retains all input
data and response history. The empty case is an identity contract, not halt. -/
namespace CryptoOracle.Interactive.CountedRejectionIteration
open Foundation.Probability Foundation.Symmetric TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

structure Value (State : Type u) where
  past : List (Option Bool)
  markers : List Bool
  payload : List Bool
  state : State
  trace : List (List Bool × List Bool)

def frame {State : Type u} (input : Value State) : Configuration State :=
  ⟨input.state, .running (CountedCaller.waiting input.past input.markers input.payload), input.trace⟩

def next {State : Type u} (input : Value State) (bit : Bool) : Value State :=
  match input.markers with
  | [] => input
  | marker :: markers =>
      { input with
        past := some marker :: input.past
        markers := markers
        trace := ([bit], [false]) :: input.trace }

variable {State : Type u} {width : Nat} (native : Machine.Program) (oracle : BitOracle State)
    (key : Bits width) (hMismatch : width ≠ 1)

noncomputable def single : Value State → Procedure (OneUseSource.step native CountedCaller.code oracle) Unit (Value State)
  | ⟨past, [], payload, state, trace⟩ =>
      Procedure.ofFixed _
        (fun _ => .source false (Machine.PairPreparation.operand [] key.toList []) (frame ⟨past, [], payload, state, trace⟩))
        (fun _ output => .source false (Machine.PairPreparation.operand [] key.toList []) (frame output))
        (fun _ => PMF.pure ⟨past, [], payload, state, trace⟩) (fun _ => 0)
        (fun _ => by simp [TimedExecution.eval, PMF.pure_map])
  | ⟨past, marker :: markers, payload, state, trace⟩ =>
      (CountedRejection.observed native oracle key state trace past marker markers payload hMismatch).observe
        (fun bit => next ⟨past, marker :: markers, payload, state, trace⟩ bit)
        (fun _ output => .source false (Machine.PairPreparation.operand [] key.toList []) (frame output))
        (fun _ _ _ => rfl)

noncomputable def round : Procedure (OneUseSource.step native CountedCaller.code oracle) (Value State) (Value State) :=
  Procedure.dispatch (single native oracle key hMismatch)

theorem entry (input : Value State) : (round native oracle key hMismatch).entry input =
    .source false (Machine.PairPreparation.operand [] key.toList []) (frame input) := by
  rcases input with ⟨past, markers, payload, state, trace⟩
  cases markers <;> rfl

theorem exit (input output : Value State) : (round native oracle key hMismatch).exit input output =
    .source false (Machine.PairPreparation.operand [] key.toList []) (frame output) := by
  rcases input with ⟨past, markers, payload, state, trace⟩
  cases markers <;> rfl

theorem bound (input : Value State) : (round native oracle key hMismatch).budget input ≤ 12 * min width 1 + 36 := by
  rcases input with ⟨past, markers, payload, state, trace⟩
  cases markers with
  | nil => exact Nat.zero_le _
  | cons marker markers =>
      change (CountedRejection.round native oracle key state trace past marker markers payload hMismatch).budget () ≤ _
      rw [CountedRejection.budget]

theorem returns (input output : Value State)
    (_ : output ∈ ((round native oracle key hMismatch).semantics input).support) :
    (round native oracle key hMismatch).exit input output = (round native oracle key hMismatch).entry output := by
  rw [exit, entry]

theorem semantics (input : Value State) : (round native oracle key hMismatch).semantics input =
    sampleBit.map (next input) := by
  rcases input with ⟨past, markers, payload, state, trace⟩
  cases markers with
  | nil =>
      change PMF.pure ⟨past, [], payload, state, trace⟩ =
        sampleBit.map (Function.const Bool (⟨past, [], payload, state, trace⟩ : Value State))
      rw [PMF.map_const]
  | cons marker markers =>
      change ((CountedRejection.observed native oracle key state trace past marker markers payload hMismatch).semantics ()).map _ = _
      rw [CountedRejection.observed_semantics]

noncomputable def kernel : Value State → PMF (Value State × Nat)
  | input@⟨_, [], _, _, _⟩ => PMF.pure (input, 0)
  | input@⟨past, marker :: markers, payload, state, trace⟩ =>
      (CountedRejection.publicCost state trace past marker markers payload hMismatch).map
        (fun result => (next input result.1, result.2))

theorem costed (input : Value State) : (round native oracle key hMismatch).costed input = kernel hMismatch input := by
  rcases input with ⟨past, markers, payload, state, trace⟩
  cases markers with
  | nil => simp [round, Procedure.dispatch, single, Procedure.ofFixed, kernel, PMF.pure_map]
  | cons marker markers =>
      change ((CountedRejection.observed native oracle key state trace past marker markers payload hMismatch).costed ()).map _ = _
      rw [CountedRejection.observed_costed]
      rfl

noncomputable def execution (rounds : Nat) :=
  (round native oracle key hMismatch).iterate (12 * min width 1 + 36)
    (bound native oracle key hMismatch) (returns native oracle key hMismatch) rounds

theorem execution_budget (rounds : Nat) (input : Value State) :
    (execution native oracle key hMismatch rounds).budget input = rounds * (12 * min width 1 + 36) :=
  Procedure.iterate_budget _ _ _ _ _ _

theorem execution_entry (rounds : Nat) (input : Value State) :
    (execution native oracle key hMismatch rounds).entry input =
      .source false (Machine.PairPreparation.operand [] key.toList []) (frame input) := by
  unfold execution
  rw [Procedure.iterate_entry, entry]

theorem execution_exit (rounds : Nat) (input output : Value State) :
    (execution native oracle key hMismatch rounds).exit input output =
      .source false (Machine.PairPreparation.operand [] key.toList []) (frame output) := by
  unfold execution
  rw [Procedure.iterate_exit, entry]

theorem execution_costed (rounds : Nat) (input : Value State) :
    (execution native oracle key hMismatch rounds).costed input = CostedIteration.eval (kernel hMismatch) rounds input := by
  unfold execution
  rw [Procedure.iterate_costed_eval]
  have he : (round native oracle key hMismatch).costed = kernel hMismatch := funext (costed native oracle key hMismatch)
  rw [he]

theorem remaining (rounds : Nat) (input output : Value State)
    (h : output ∈ ((execution native oracle key hMismatch rounds).semantics input).support) :
    output.markers.length = input.markers.length - rounds := by
  induction rounds generalizing input output with
  | zero =>
      change output ∈ (PMF.pure input).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      simp
  | succ rounds ih =>
      unfold execution at h
      rw [Procedure.iterate_semantics_succ, semantics, PMF.mem_support_bind_iff] at h
      obtain ⟨middle, hMiddle, hOutput⟩ := h
      rw [PMF.mem_support_map_iff] at hMiddle
      obtain ⟨bit, _, he⟩ := hMiddle
      subst middle
      have hf := ih (next input bit) output hOutput
      have hn : (next input bit).markers.length = input.markers.length - 1 := by
        cases hm : input.markers <;> simp [next, hm]
      rw [hn] at hf
      omega

theorem reaches_separator (input output : Value State)
    (h : output ∈ ((execution native oracle key hMismatch input.markers.length).semantics input).support) :
    output.markers = [] := by
  have he := remaining native oracle key hMismatch input.markers.length input output h
  simpa using he

/-- Any logical observation preserved by one round is preserved by the
actual finite execution. This includes data carried to the normal call. -/
theorem preserves {Observed : Type v} (view : Value State → Observed)
    (hView : ∀ input bit, view (next input bit) = view input)
    (rounds : Nat) (input output : Value State)
    (h : output ∈ ((execution native oracle key hMismatch rounds).semantics input).support) :
    view output = view input := by
  induction rounds generalizing input output with
  | zero =>
      change output ∈ (PMF.pure input).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      rfl
  | succ rounds ih =>
      unfold execution at h
      rw [Procedure.iterate_semantics_succ, semantics, PMF.mem_support_bind_iff] at h
      obtain ⟨middle, hMiddle, hOutput⟩ := h
      rw [PMF.mem_support_map_iff] at hMiddle
      obtain ⟨bit, _, he⟩ := hMiddle
      subst middle
      exact (ih _ _ hOutput).trans (hView input bit)

theorem payload_preserved (rounds : Nat) (input output : Value State)
    (h : output ∈ ((execution native oracle key hMismatch rounds).semantics input).support) :
    output.payload = input.payload := by
  apply preserves native oracle key hMismatch Value.payload _ rounds input output h
  intro input bit
  cases hm : input.markers <;> simp [next, hm]

theorem state_preserved (rounds : Nat) (input output : Value State)
    (h : output ∈ ((execution native oracle key hMismatch rounds).semantics input).support) :
    output.state = input.state := by
  apply preserves native oracle key hMismatch Value.state _ rounds input output h
  intro input bit
  cases hm : input.markers <;> simp [next, hm]

/-- The full result and actual accumulated cost have a common law for any
private key and encryption program. This is not a secrecy claim about payload. -/
theorem execution_costed_eq (otherNative : Machine.Program) (otherKey : Bits width)
    (rounds : Nat) (input : Value State) :
    (execution native oracle key hMismatch rounds).costed input =
      (execution otherNative oracle otherKey hMismatch rounds).costed input := by
  rw [execution_costed, execution_costed]

/-- Continue the same physical machine for the unused portion of the horizon;
contract completion does not halt or reset the caller. -/
theorem resume_law (rounds : Nat) (input : Value State) (horizon : Nat)
    (hHorizon : rounds * (12 * min width 1 + 36) ≤ horizon) :
    TimedExecution.eval (OneUseSource.step native CountedCaller.code oracle) horizon
      (.source false (Machine.PairPreparation.operand [] key.toList []) (frame input)) =
      (CostedIteration.eval (kernel hMismatch) rounds input).bind (fun result =>
        TimedExecution.eval (OneUseSource.step native CountedCaller.code oracle)
          (horizon - result.2)
          (.source false (Machine.PairPreparation.operand [] key.toList []) (frame result.1))) := by
  have h := (execution native oracle key hMismatch rounds).law input horizon
    (by rw [execution_budget]; exact hHorizon)
  rw [execution_entry, execution_costed] at h
  simp only [execution_exit] at h
  exact h

/-- The suffix reads the retained payload using the same fixed caller code.
Its entry has no remaining markers; sequencing proves that condition. -/
noncomputable def normalPreparation : Procedure
    (OneUseSource.step native CountedCaller.code oracle) (Value State) Unit :=
  Procedure.dispatch (fun input : Value State =>
    (CountedCaller.preparation native oracle
      (Machine.PairPreparation.operand [] key.toList []) input.state input.trace).reindex
        (fun _ : Unit => (input.past, input.payload)))

theorem preparation_handoff (input output : Value State)
    (h : output ∈ ((execution native oracle key hMismatch input.markers.length).semantics input).support) :
    (normalPreparation native oracle key).entry output =
      (execution native oracle key hMismatch input.markers.length).exit input output := by
  rw [execution_exit]
  have hm := reaches_separator native oracle key hMismatch input output h
  change OneUseSource.Control.source false _
      ⟨output.state, .running (CountedCaller.waiting output.past [] output.payload), output.trace⟩ = _
  simp only [frame, hm]

/-- Any finite marker list, any payload, any private native program: execute
all rejections and reach the normal call without resetting the machine. -/
noncomputable def prepare (input : Value State) :=
  ((execution native oracle key hMismatch input.markers.length).reindex (fun _ : Unit => input)).seq
    (normalPreparation native oracle key)
    (fun _ output h => preparation_handoff native oracle key hMismatch input output h)
    (fun _ => 11 * input.payload.length + 8)
    (fun _ output h => by
      change 11 * output.payload.length + 8 ≤ 11 * input.payload.length + 8
      rw [payload_preserved native oracle key hMismatch input.markers.length input output h])

theorem prepare_budget (input : Value State) :
    (prepare native oracle key hMismatch input).budget () =
      input.markers.length * (12 * min width 1 + 36) + 11 * input.payload.length + 8 := by
  change (execution native oracle key hMismatch input.markers.length).budget input +
    (11 * input.payload.length + 8) = _
  rw [execution_budget]
  omega

theorem prepare_entry (input : Value State) :
    (prepare native oracle key hMismatch input).entry () =
      .source false (Machine.PairPreparation.operand [] key.toList []) (frame input) :=
  execution_entry native oracle key hMismatch input.markers.length input

theorem prepare_exit (input : Value State) (output : Value State × Unit) :
    (prepare native oracle key hMismatch input).exit () output =
      CodeRelocation.oneUse CountedCaller.before.length
        (.source false (Machine.PairPreparation.operand [] key.toList [])
          ⟨output.1.state, .running (CountedCaller.ready output.1.past output.1.payload), output.1.trace⟩) := rfl

theorem prepare_semantics (input : Value State) :
    (prepare native oracle key hMismatch input).semantics () =
      ((execution native oracle key hMismatch input.markers.length).semantics input).map
        (fun output => (output, ())) := by
  simp [prepare, Procedure.seq, Procedure.reindex, normalPreparation,
    Procedure.dispatch, CountedCaller.preparation, Procedure.ofFixed, PMF.pure_map,
    PMF.map, Function.comp_def]

/-- Preserve the actual round costs and charge the suffix's real copy cost. -/
theorem prepare_costed (input : Value State) :
    (prepare native oracle key hMismatch input).costed () =
      (CostedIteration.eval (kernel hMismatch) input.markers.length input).map
        (fun result => ((result.1, ()), result.2 + (11 * result.1.payload.length + 8))) := by
  change ((execution native oracle key hMismatch input.markers.length).costed input).bind
    (fun middle => ((normalPreparation native oracle key).costed middle.1).map
      (fun output => ((middle.1, output.1), middle.2 + output.2))) = _
  rw [execution_costed]
  simp [normalPreparation, Procedure.dispatch, CountedCaller.preparation,
    Procedure.reindex, Procedure.ofFixed, PMF.pure_map, PMF.map, Function.comp_def]

theorem prepare_costed_eq (otherNative : Machine.Program) (otherKey : Bits width)
    (input : Value State) :
    (prepare native oracle key hMismatch input).costed () =
      (prepare otherNative oracle otherKey hMismatch input).costed () := by
  rw [prepare_costed, prepare_costed]

/-- Remove the carried payload from the logical observation, while retaining
the marker prefix, external state, and complete rejection history. -/
def erasePayload (input : Value State) : Value State := { input with payload := [] }

theorem erasePayload_next (input : Value State) (bit : Bool) :
    erasePayload (next input bit) = next (erasePayload input) bit := by
  cases hm : input.markers <;> simp [erasePayload, next, hm]

theorem kernel_erasePayload (input : Value State) :
    (kernel hMismatch input).map (CostedIteration.project erasePayload) =
      kernel hMismatch (erasePayload input) := by
  rcases input with ⟨past, markers, payload, state, trace⟩
  cases markers with
  | nil => simp [kernel, erasePayload, CostedIteration.project, PMF.pure_map]
  | cons marker markers =>
      simp only [kernel, PMF.map_comp, CostedIteration.project, Function.comp_def,
        erasePayload_next]
      rw [CountedRejection.publicCost_payload state trace past marker markers payload hMismatch []]
      rfl

theorem execution_public_cost (rounds : Nat) (input : Value State) :
    ((execution native oracle key hMismatch rounds).costed input).map
      (CostedIteration.project erasePayload) =
      CostedIteration.eval (kernel hMismatch) rounds (erasePayload input) := by
  rw [execution_costed]
  exact CostedIteration.eval_map _ _ _ (kernel_erasePayload hMismatch) rounds input

theorem prepare_public_cost (input : Value State) :
    ((prepare native oracle key hMismatch input).costed ()).map
      (fun result => (erasePayload result.1.1, result.2)) =
      (CostedIteration.eval (kernel hMismatch) input.markers.length (erasePayload input)).map
        (fun result => (result.1, result.2 + (11 * input.payload.length + 8))) := by
  rw [← execution_public_cost native oracle key hMismatch input.markers.length input,
    prepare_costed, execution_costed, PMF.map_comp, PMF.map_comp]
  rw [PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  have hs : result ∈ ((execution native oracle key hMismatch input.markers.length).costed input).support := by
    rwa [execution_costed]
  have hp := payload_preserved native oracle key hMismatch input.markers.length input result.1
    ((execution native oracle key hMismatch input.markers.length).result_support input result hs)
  simp only [Function.comp_def, CostedIteration.project, hp]

end CryptoOracle.Interactive.CountedRejectionIteration
