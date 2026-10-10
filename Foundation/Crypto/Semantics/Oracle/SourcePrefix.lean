import Foundation.Crypto.Semantics.Oracle.OneUseSource
import Foundation.Crypto.Semantics.ProcedureSimulation

/-! The source chooses its first request without consulting the private key.
The local evaluator stops at a real captured request or genuine termination;
lifting retains the first-arrival cost and continues the actual outer runtime. -/
namespace CryptoOracle.Interactive.SourcePrefix
open Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

def boundary (frame : Configuration State) : Bool :=
  match frame.control with
  | .awaiting _ _ => true
  | _ => Reification.terminal frame.control

noncomputable def step (code : Code) (oracle : BitOracle State) (frame : Configuration State) : PMF (Configuration State) :=
  if boundary frame then PMF.pure frame else Reification.timedStep code oracle frame

variable (code : Code) (oracle : BitOracle State)

theorem collect (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (bits reversed : List Bool)
    (before after : List (Option Bool)) :
    TimedExecution.eval (step code oracle) (bits.length + 1)
      (⟨state, .sending machine (RequestExport.packetTape before after bits) reversed, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .reversing machine (bits.reverse ++ reversed) [], trace⟩ := by
  induction bits generalizing reversed before with
  | nil => simp [TimedExecution.eval, step, boundary, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition, RequestExport.packetTape]
  | cons bit bits ih =>
      rw [show (bit :: bits).length + 1 = (bits.length + 1) + 1 by rfl, TimedExecution.eval]
      simp only [step, boundary, Reification.terminal, Bool.false_eq_true, ↓reduceIte,
        Reification.timedStep, Reification.perform, Reification.action, transition,
        RequestExport.packetTape, List.map_cons, List.cons_append, List.headD_cons, List.tail_cons,
        Machine.Tape.moveRight, PMF.pure_bind]
      cases bits <;>
        simpa [RequestExport.packetTape, List.reverse_cons, List.append_assoc] using
          ih (bit :: reversed) (some bit :: before)

theorem reverse (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (remaining request : List Bool) :
    TimedExecution.eval (step code oracle) (remaining.length + 1)
      (⟨state, .reversing machine remaining request, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .awaiting machine (remaining.reverse ++ request), trace⟩ := by
  induction remaining generalizing request with
  | nil => simp [TimedExecution.eval, step, boundary, Reification.timedStep, Reification.terminal,
      Reification.perform, Reification.action, transition]
  | cons bit remaining ih =>
      rw [show (bit :: remaining).length + 1 = (remaining.length + 1) + 1 by rfl, TimedExecution.eval]
      simp only [step, boundary, Reification.terminal, Bool.false_eq_true, ↓reduceIte,
        Reification.timedStep, Reification.perform, Reification.action, transition, PMF.pure_bind]
      simpa [List.reverse_cons, List.append_assoc] using ih (bit :: request)

theorem capture_run (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (before after : List (Option Bool)) (hActive : machine.halted = false)
    (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape before after request) :
    TimedExecution.eval (step code oracle) (2 * request.length + 3)
      (⟨state, .running machine, trace⟩ : Configuration State) =
      PMF.pure ⟨state, .awaiting machine.advance request, trace⟩ := by
  rw [show 2 * request.length + 3 = (2 * request.length + 2) + 1 by omega, TimedExecution.eval]
  simp only [step, boundary, Reification.timedStep, Reification.terminal, hActive, Bool.false_eq_true,
    ↓reduceIte, Reification.perform, Reification.action, transition, hCall, PMF.pure_bind]
  rw [hTape, show 2 * request.length + 2 = (request.length + 1) + (request.reverse.length + 1) by simp; omega,
    TimedExecution.eval_add, collect, PMF.pure_bind]
  simp only [List.append_nil]
  rw [reverse]
  simp

structure Input where
  start : Configuration State
  budget : Nat
  complete : ∀ frame ∈ (TimedExecution.eval (step code oracle) budget start).support, boundary frame = true

noncomputable def localProcedure : Procedure (step code oracle) (Input code oracle) (Configuration State) :=
  Procedure.ofFixed _ Input.start (fun _ frame => frame)
    (fun input => TimedExecution.eval (step code oracle) input.budget input.start) Input.budget
    (fun _ => (PMF.map_id _).symm)

/-- Reuse the source's actual first request/termination boundary in any
continuing runtime with the same pre-boundary source transitions. -/
noncomputable def liftTo {Target : Type*} (targetStep : Target → PMF Target)
    (targetBoundary : Target → Bool) (embed : Configuration State → Target)
    (hBoundary : ∀ frame, targetBoundary (embed frame) = boundary frame)
    (hStep : ∀ frame, boundary frame = false →
      targetStep (embed frame) = (step code oracle frame).map embed) :=
  (localProcedure code oracle).liftBoundary boundary (fun input _ h => input.complete _ h)
    (fun frame h => by simp [step, h]) (fun _ frame => frame) (fun _ _ => rfl)
    targetStep targetBoundary embed hBoundary hStep

def targetBoundary : OneUseSource.Control State → Bool
  | .source _ _ frame => boundary frame
  | _ => true

variable (native : Machine.Program) (key : Machine.Tape)

noncomputable def procedure :=
  liftTo code oracle (OneUseSource.step native code oracle) targetBoundary
    (OneUseSource.Control.source false key) (fun _ => rfl)
    (fun frame h => by
      cases hc : frame.control <;> simp_all [boundary, step, OneUseSource.step])

theorem budget (input : Input code oracle) :
    (procedure code oracle native key).budget input = input.budget := rfl

theorem semantics (input : Input code oracle) :
    (procedure code oracle native key).semantics input =
      TimedExecution.eval (step code oracle) input.budget input.start := rfl

/-- The source configuration and exact first-arrival cost are independent
of the hidden key and the native handler program. -/
theorem cost_independence (input : Input code oracle)
    (firstNative secondNative : Machine.Program) (firstKey secondKey : Machine.Tape) :
    (procedure code oracle firstNative firstKey).costed input =
      (procedure code oracle secondNative secondKey).costed input := rfl

theorem boundary_distribution (input : Input code oracle) :
    ((procedure code oracle native key).costed input).map Prod.fst =
      TimedExecution.eval (step code oracle) input.budget input.start :=
  (procedure code oracle native key).correct input

theorem resume_law (input : Input code oracle) (horizon : Nat) (hBudget : input.budget ≤ horizon) :
    TimedExecution.eval (OneUseSource.step native code oracle) horizon
      (.source false key input.start) =
      ((procedure code oracle native key).costed input).bind
        (fun result => TimedExecution.eval (OneUseSource.step native code oracle) (horizon - result.2)
          (.source false key result.1)) :=
  (procedure code oracle native key).law input horizon hBudget
section Composition
variable {Output : Type v}
    (continuation : Procedure (OneUseSource.step native code oracle) (Configuration State) Output)
    (hEntry : ∀ frame, continuation.entry frame = .source false key frame)
    (cap : Input code oracle → Nat)
    (hCap : ∀ input frame, frame ∈ ((procedure code oracle native key).semantics input).support →
      continuation.budget frame ≤ cap input)

/-- The continuation receives the actual selected request, caller state and
trace. Its bound must hold for every reachable selection, including termination. -/
noncomputable def compose :=
  (procedure code oracle native key).seq continuation (fun _ frame _ => hEntry frame)
    cap hCap

theorem compose_budget (input : Input code oracle) :
    (compose code oracle native key continuation hEntry cap hCap).budget input = input.budget + cap input := rfl

theorem compose_semantics (input : Input code oracle) :
    (compose code oracle native key continuation hEntry cap hCap).semantics input =
      (TimedExecution.eval (step code oracle) input.budget input.start).bind
        (fun frame => (continuation.semantics frame).map (fun output => (frame, output))) := rfl
end Composition
def next (frame : Configuration State) : OneUseSource.Control State :=
  match frame.control with
  | .awaiting saved request => .handling false saved frame.state frame.reverseTrace request
      (.preparing (.preparing (.reading key saved.outputTape {})))
  | _ => .source false key frame

theorem handoff_boundary (frame : Configuration State) (h : boundary frame = true) :
    OneUseSource.step native code oracle (.source false key frame) = PMF.pure (next key frame) := by
  cases hc : frame.control <;>
    simp_all [boundary, next, OneUseSource.step, Reification.timedStep, Reification.terminal, PMF.pure_map]

noncomputable def handoff : Procedure (OneUseSource.step native code oracle)
    (Configuration State) (OneUseSource.Control State) :=
  Procedure.ofFixed _ (OneUseSource.Control.source false key) (fun _ result => result)
    (fun frame => OneUseSource.step native code oracle (.source false key frame)) (fun _ => 1)
    (fun frame => by
      simp only [TimedExecution.eval, PMF.bind_pure]
      exact (PMF.map_id _).symm)

/-- One additional charged transition enters the actual handler, or retains
an already terminated caller. No source request is manufactured by the proof. -/
noncomputable def toHandler :=
  compose code oracle native key (handoff code oracle native key) (fun _ => rfl)
    (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

theorem toHandler_budget (input : Input code oracle) :
    (toHandler code oracle native key).budget input = input.budget + 1 := rfl

theorem toHandler_distribution (input : Input code oracle) :
    ((toHandler code oracle native key).costed input).map
      (fun result => (toHandler code oracle native key).exit input result.1) =
      (TimedExecution.eval (step code oracle) input.budget input.start).map (next key) := by
  have h := congrArg (fun distribution => distribution.map ((toHandler code oracle native key).exit input))
    ((toHandler code oracle native key).correct input)
  simp only [PMF.map_comp, Function.comp_def] at h
  have hs : (toHandler code oracle native key).semantics input =
      (TimedExecution.eval (step code oracle) input.budget input.start).bind
        (fun frame => ((handoff code oracle native key).semantics frame).map (fun output => (frame, output))) := rfl
  rw [hs] at h
  simp only [handoff, Procedure.ofFixed, PMF.map_bind, PMF.map_comp, Function.comp_def] at h
  have he : ∀ frame ∈ (TimedExecution.eval (step code oracle) input.budget input.start).support,
      (OneUseSource.step native code oracle (.source false key frame)).map
        (fun output => (toHandler code oracle native key).exit input (frame, output)) = PMF.pure (next key frame) := by
    intro frame hFrame
    rw [handoff_boundary code oracle native key frame (input.complete frame hFrame), PMF.pure_map]
    rfl
  rw [← PMF.bindOnSupport_eq_bind] at h
  have hb : (TimedExecution.eval (step code oracle) input.budget input.start).bindOnSupport
      (fun frame _ => (OneUseSource.step native code oracle (.source false key frame)).map
        (fun output => (toHandler code oracle native key).exit input (frame, output))) =
      (TimedExecution.eval (step code oracle) input.budget input.start).bindOnSupport
        (fun frame _ => PMF.pure (next key frame)) := by
    congr 1
    funext frame hFrame
    exact he frame hFrame
  rw [hb] at h
  rw [PMF.bindOnSupport_eq_bind] at h
  simpa only [PMF.map, Function.comp_def] using h
end CryptoOracle.Interactive.SourcePrefix
