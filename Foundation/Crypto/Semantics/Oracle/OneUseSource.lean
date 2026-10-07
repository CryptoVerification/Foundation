import Foundation.Crypto.Semantics.Oracle.CheckedCallback
import Foundation.Crypto.Semantics.OneUseCounter
import Foundation.Crypto.Semantics.Oracle.RequestExport

/-! A finite outer controller captures real source requests and enforces
one-use acceptance. Invalid lengths do not consume the key. Spent keys route
directly to physical rejection writing, without starting the native handler. -/
namespace CryptoOracle.Interactive.OneUseSource
open Foundation.Probability TimedExecution
universe u

inductive Control (State : Type u) where
  | source (used : Bool) (key : Machine.Tape) (frame : Configuration State)
  | handling (used : Bool) (saved : Machine.Configuration) (state : State)
      (trace : List (List Bool × List Bool)) (request : List Bool) (handler : CheckedCallback.Control State)

def used {State : Type u} : Control State → Bool
  | .source spent _ _ => spent
  | .handling spent _ _ _ _ _ => spent

def accepted {State : Type u} : Control State → Bool
  | .handling false _ _ _ _ (.preparing (.preparing (.ready _ _ _))) => true
  | _ => false

noncomputable def step {State : Type u} (native : Machine.Program) (code : Code)
    (oracle : BitOracle State) : Control State → PMF (Control State)
  | .source spent key frame =>
      match frame.control with
      | .awaiting saved request =>
          PMF.pure (.handling spent saved frame.state frame.reverseTrace request
            (if spent then .tagging key saved.outputTape (.start none)
             else .preparing (.preparing (.reading key saved.outputTape {}))))
      | _ => (Reification.timedStep code oracle frame).map (.source spent key)
  | .handling spent saved state trace request (.preparing (.preparing (.ready key second buffer))) =>
      if spent then PMF.pure (.handling true saved state trace request (.tagging key second (.start none)))
      else PMF.pure (.handling true saved state trace request (.computing key second (.running { inputTape := buffer })))
  | .handling spent _ _ _ _ (.calling key _ (.source ⟨state, .running machine, trace⟩)) =>
      PMF.pure (.source spent key ⟨state, .running machine, trace⟩)
  | .handling spent saved state trace request handler =>
      (CheckedCallback.step native code oracle saved state trace request handler).map
        (.handling spent saved state trace request)

theorem accepted_unused {State : Type u} (start : Control State) :
    accepted start = true → used start = false := by
  cases start with
  | source spent key frame => simp [accepted]
  | handling spent saved state trace request handler =>
      cases handler <;> try simp [accepted]
      rename_i preparation
      cases preparation <;> try simp
      rename_i preparation
      cases preparation <;> cases spent <;> simp [used]

private theorem mapped_used {State : Type u} {A : Type*} (distribution : PMF A)
    (embed : A → Control State) (spent : Bool) (next : Control State) (h : next ∈ (distribution.map embed).support)
    (hUsed : ∀ value, used (embed value) = spent) : used next = spent := by
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨value, _, he⟩ := h
  subst next
  exact hUsed value

theorem status {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (start next : Control State) (h : next ∈ (step native code oracle start).support) :
    used next = (used start || accepted start) := by
  cases start with
  | source spent key frame =>
      cases hc : frame.control <;> simp only [step, hc] at h
      all_goals simp only [used, accepted, Bool.or_false]
      all_goals first
        | (rw [PMF.mem_support_pure_iff] at h; subst next; rfl)
        | (exact mapped_used _ _ spent next h (fun _ => rfl))
  | handling spent saved state trace request handler =>
      cases handler with
      | preparing preparation =>
          cases preparation with
          | preparing preparation =>
              cases preparation <;> cases spent <;>
                simp only [step, Bool.false_eq_true, ↓reduceIte] at h
              all_goals simp only [used, accepted, Bool.or_false, Bool.false_or]
              all_goals first
                | (rw [PMF.mem_support_pure_iff] at h; subst next; rfl)
                | (exact mapped_used _ _ _ next h (fun _ => rfl))
          | failure recovery =>
              simp only [step] at h
              simp only [used, accepted, Bool.or_false]
              exact mapped_used _ _ spent next h (fun _ => rfl)
      | computing first second component =>
          simp only [step] at h
          simp only [used, accepted, Bool.or_false]
          exact mapped_used _ _ spent next h (fun _ => rfl)
      | tagging first second packet =>
          simp only [step] at h
          simp only [used, accepted, Bool.or_false]
          exact mapped_used _ _ spent next h (fun _ => rfl)
      | calling first second callback =>
          cases callback with
          | responding component =>
              simp only [step] at h
              simp only [used, accepted, Bool.or_false]
              exact mapped_used _ _ spent next h (fun _ => rfl)
          | source frame =>
              rcases frame with ⟨newState, control, newTrace⟩
              cases control <;> simp only [step] at h
              all_goals simp only [used, accepted, Bool.or_false]
              all_goals first
                | (rw [PMF.mem_support_pure_iff] at h; subst next; rfl)
                | (exact mapped_used _ _ spent next h (fun _ => rfl))

theorem at_most_one {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (fuel : Nat) (start : Control State) (result : Control State × Nat)
    (h : result ∈ (TimedExecution.eval (OneUseCounter.countedStep (step native code oracle) accepted) fuel (start, 0)).support) :
    result.2 ≤ 1 :=
  OneUseCounter.at_most_one (step native code oracle) used accepted accepted_unused
    (status native code oracle) fuel start result h

theorem spent_preserved {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (fuel : Nat) (start next : Control State) (hUsed : used start = true)
    (hNext : next ∈ (TimedExecution.eval (step native code oracle) fuel start).support) : used next = true := by
  apply eval_preserves (step native code oracle) (fun control => used control = true) _ fuel start next hUsed hNext
  intro control hControl result hResult
  rw [status native code oracle control result hResult, hControl]
  rfl

theorem spent_not_accepted {State : Type u} (control : Control State) (hUsed : used control = true) :
    accepted control = false := by
  cases hEvent : accepted control with
  | false => rfl
  | true => have h := accepted_unused control hEvent; simp_all

theorem fresh_accept {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (saved : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    (request : List Bool) (key second buffer : Machine.Tape) :
    TimedExecution.eval (step native code oracle) 1
      (.handling false saved state trace request (.preparing (.preparing (.ready key second buffer)))) =
      PMF.pure (.handling true saved state trace request (.computing key second (.running { inputTape := buffer }))) := by
  simp [TimedExecution.eval, step]

theorem spent_prepared_reject {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (saved : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    (request : List Bool) (key second buffer : Machine.Tape) :
    TimedExecution.eval (step native code oracle) 1
      (.handling true saved state trace request (.preparing (.preparing (.ready key second buffer)))) =
      PMF.pure (.handling true saved state trace request (.tagging key second (.start none))) := by
  simp [TimedExecution.eval, step]

theorem resume_transfer {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (spent : Bool) (saved machine : Machine.Configuration) (savedState state : State)
    (savedTrace trace : List (List Bool × List Bool)) (request : List Bool) (key second : Machine.Tape) :
    TimedExecution.eval (step native code oracle) 1
      (.handling spent saved savedState savedTrace request (.calling key second (.source ⟨state, .running machine, trace⟩))) =
      PMF.pure (.source spent key ⟨state, .running machine, trace⟩) := by
  simp [TimedExecution.eval, step]

/-- Already-spent requests never enter native computation. Includes physical
failure writing, export, loading, history update and the outer return. -/
theorem spent_reply {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (saved : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    (request : List Bool) (key second : Machine.Tape) :
    TimedExecution.eval (step native code oracle) 18
      (.handling true saved state trace request (.tagging key second (.start none))) =
      PMF.pure (.source true key (NativeCallback.resumed saved state trace request [false])) := by
  simp [TimedExecution.eval, step, CheckedCallback.step, Machine.ResponsePacket.step,
    Machine.ResponseExport.step, NativeCallback.step, NativeCallback.loading, NativeCallback.resumed,
    Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition,
    Machine.Tape.write, Machine.Tape.moveRight, Machine.Tape.moveLeft,
    ResponseLoading.loaded, ResponseLoading.fromCells, PMF.pure_map]

variable {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)

theorem collect (spent : Bool) (key : Machine.Tape) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (bits reversed : List Bool)
    (before after : List (Option Bool)) :
    TimedExecution.eval (step native code oracle) (bits.length + 1)
      (.source spent key ⟨state, .sending machine (RequestExport.packetTape before after bits) reversed, trace⟩) =
      PMF.pure (.source spent key ⟨state, .reversing machine (bits.reverse ++ reversed) [], trace⟩) := by
  induction bits generalizing reversed before with
  | nil =>
      simp [TimedExecution.eval, step, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, RequestExport.packetTape, PMF.pure_map]
  | cons bit bits ih =>
      rw [show (bit :: bits).length + 1 = (bits.length + 1) + 1 by rfl, TimedExecution.eval]
      simp only [step, Reification.timedStep, Reification.terminal, Bool.false_eq_true, ↓reduceIte,
        Reification.perform, Reification.action, transition, RequestExport.packetTape, List.map_cons,
        List.cons_append, List.headD_cons, List.tail_cons, Machine.Tape.moveRight, PMF.pure_map, PMF.pure_bind]
      cases bits <;> simpa [RequestExport.packetTape, List.reverse_cons, List.append_assoc]
        using ih (bit :: reversed) (some bit :: before)

theorem reverse (spent : Bool) (key : Machine.Tape) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (remaining request : List Bool) :
    TimedExecution.eval (step native code oracle) (remaining.length + 1)
      (.source spent key ⟨state, .reversing machine remaining request, trace⟩) =
      PMF.pure (.source spent key ⟨state, .awaiting machine (remaining.reverse ++ request), trace⟩) := by
  induction remaining generalizing request with
  | nil =>
      simp [TimedExecution.eval, step, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, PMF.pure_map]
  | cons bit remaining ih =>
      rw [show (bit :: remaining).length + 1 = (remaining.length + 1) + 1 by rfl, TimedExecution.eval]
      simp only [step, Reification.timedStep, Reification.terminal, Bool.false_eq_true, ↓reduceIte,
        Reification.perform, Reification.action, transition, PMF.pure_map, PMF.pure_bind]
      simpa [List.reverse_cons, List.append_assoc] using ih (bit :: request)

theorem export_run (spent : Bool) (key : Machine.Tape) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (before after : List (Option Bool)) :
    TimedExecution.eval (step native code oracle) (2 * request.length + 2)
      (.source spent key ⟨state, .sending machine (RequestExport.packetTape before after request) [], trace⟩) =
      PMF.pure (.source spent key ⟨state, .awaiting machine request, trace⟩) := by
  rw [show 2 * request.length + 2 = (request.length + 1) + (request.reverse.length + 1) by simp; omega,
    TimedExecution.eval_add, collect, PMF.pure_bind]
  simp only [List.append_nil]
  rw [reverse]
  simp

/-- Capture, request export and transfer into physical input preparation. -/
theorem call_entry (spent : Bool) (key : Machine.Tape) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (before after : List (Option Bool)) (hActive : machine.halted = false)
    (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape before after request) :
    TimedExecution.eval (step native code oracle) (2 * request.length + 4)
      (.source spent key ⟨state, .running machine, trace⟩) =
      PMF.pure (.handling spent machine.advance state trace request
        (if spent then .tagging key machine.outputTape (.start none)
         else .preparing (.preparing (.reading key machine.outputTape {})))) := by
  rw [show 2 * request.length + 4 = ((2 * request.length + 2) + 1) + 1 by omega, TimedExecution.eval]
  simp only [step, Reification.timedStep, Reification.terminal, hActive, Bool.false_eq_true, ↓reduceIte,
    Reification.perform, Reification.action, transition, hCall, PMF.pure_map, PMF.pure_bind]
  rw [TimedExecution.eval_add (step native code oracle) (2 * request.length + 2) 1]
  rw [hTape, export_run, PMF.pure_bind]
  simp [TimedExecution.eval, step, Machine.Configuration.advance, hTape]


end CryptoOracle.Interactive.OneUseSource
