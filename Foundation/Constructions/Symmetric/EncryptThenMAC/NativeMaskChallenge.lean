import Foundation.Constructions.Symmetric.EncryptThenMAC.NativeMaskReduction
import Foundation.Crypto.Semantics.OneUseCounter

/-! One charged external challenge query, actual cell-by-cell response loading,
two charged head moves into the retained-key layout, then the native reduction.
The response distribution belongs to the challenge experiment; its generation
is not run by or charged to the adversary. Its loading is charged explicitly. -/
namespace Foundation.Symmetric.EncryptThenMAC.NativeMaskChallenge
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC ResponseHandoffProgram
open Foundation.Examples
open ReusableBlockPad.NativeObserver (RuntimeState boundary publicMachine publicCaller decision observer)
universe u
set_option backward.isDefEq.respectTransparency false

inductive Control where
  | querying
  | loading : CryptoOracle.Interactive.Configuration Unit → Control
  | aligning : Tape → Control
  | active : NativeContinuation.Control (RuntimeState Unit) → Control

def loadCode : Code := [.native .halt]
def loaderMachine (control : CryptoOracle.Interactive.Control) : Machine.Configuration :=
  match control with | .running machine => machine | _ => {}

def loadFrame (response : List Bool) : CryptoOracle.Interactive.Configuration Unit :=
  ⟨(), .loading {} response {}, []⟩
def loadedFrame (response : List Bool) : CryptoOracle.Interactive.Configuration Unit :=
  ⟨(), .running {outputTape := ResponseLoading.loaded response, halted := true}, []⟩

variable {width : Nat} (distribution : PMF (Bits width)) (message : Bits width) (code : Program)

noncomputable def step : Control → PMF Control
  | .querying => distribution.map (fun key => .loading (loadFrame key.toList))
  | .loading frame =>
      if Reification.terminal frame.control then
        PMF.pure (.aligning (loaderMachine frame.control).outputTape.moveLeft)
      else (Reification.timedStep loadCode NativeMaskReduction.oracle frame).map .loading
  | .aligning tape => PMF.pure (.active (.producing (.active
      (.source tape.moveRight (ReusableBlockPad.callerFrame () [] message)))))
  | .active target =>
      (NativeContinuation.step (NativeMaskReduction.sourceStep message) boundary publicMachine code target).map .active

def terminal : Control → Prop
  | .active (.observing _ machine) => machine.halted = true
  | _ => False

def result : Control → Bool
  | .active target => decision target
  | _ => false

theorem absorbing (target : Control) (h : terminal target) :
    step distribution message code target = PMF.pure target := by
  cases target with
  | querying => contradiction
  | loading => contradiction
  | aligning => contradiction
  | active target =>
      cases target with
      | producing => contradiction
      | observing saved machine =>
          change machine.halted = true at h
          simp [step, NativeContinuation.step, stepPMF, next, h, PMF.pure_map]

/-- Only the querying state invokes the external challenge distribution. -/
def queries : Control → Nat
  | .querying => 0
  | _ => 1

theorem queries_le_one (target : Control) : queries target ≤ 1 := by cases target <;> simp [queries]

theorem no_second_query (start target : Control) (hStart : queries start = 1)
    (h : target ∈ (step distribution message code start).support) : queries target = 1 := by
  cases start with
  | querying => simp [queries] at hStart
  | loading frame =>
      by_cases ht : Reification.terminal frame.control = true
      · simp only [step, ht, ↓reduceIte, PMF.mem_support_pure_iff] at h
        subst target
        rfl
      · simp only [step, ht, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
        obtain ⟨_, _, rfl⟩ := h
        rfl
  | aligning tape =>
      simp only [step, PMF.mem_support_pure_iff] at h
      subst target
      rfl
  | active target =>
      simp only [step, PMF.mem_support_map_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      rfl

def queryEvent : Control → Bool
  | .querying => true
  | _ => false

theorem query_step (start target : Control) (h : target ∈ (step distribution message code start).support) :
    queries target = queries start + if queryEvent start then 1 else 0 := by
  cases start with
  | querying =>
      simp only [step, PMF.mem_support_map_iff] at h
      obtain ⟨key, _, rfl⟩ := h
      rfl
  | loading frame => exact no_second_query distribution message code _ _ rfl h
  | aligning tape => exact no_second_query distribution message code _ _ rfl h
  | active state => exact no_second_query distribution message code _ _ rfl h

/-- Ghost counting records the actual number of external query transitions.
It is proof instrumentation and does not add runtime steps. -/
theorem query_counter (fuel : Nat) (target : Control × Nat)
    (h : target ∈ (TimedExecution.eval
      (OneUseCounter.countedStep (step distribution message code) queryEvent) fuel (.querying, 0)).support) :
    target.2 = queries target.1 := by
  apply TimedExecution.eval_preserves _ (fun frame : Control × Nat => frame.2 = queries frame.1) _
    fuel (.querying, 0) target rfl h
  intro start hs next hn
  rw [OneUseCounter.countedStep, PMF.mem_support_map_iff] at hn
  obtain ⟨next, hn, rfl⟩ := hn
  simp only
  rw [hs, query_step distribution message code start.1 next hn]

theorem at_most_one_query (fuel : Nat) (target : Control × Nat)
    (h : target ∈ (TimedExecution.eval
      (OneUseCounter.countedStep (step distribution message code) queryEvent) fuel (.querying, 0)).support) :
    target.2 ≤ 1 := by
  rw [query_counter distribution message code fuel target h]
  exact queries_le_one _

noncomputable def query : TimedExecution.Procedure (step distribution message code) Unit (Bits width) :=
  TimedExecution.Procedure.ofFixed _ (fun _ => .querying)
    (fun _ key => .loading (loadFrame key.toList)) (fun _ => distribution) (fun _ => 1)
    (fun _ => by simp [TimedExecution.eval, step, PMF.bind_pure])

private noncomputable def halt (key : Bits width) :=
  TimedExecution.Procedure.ofFixed (Reification.timedStep loadCode NativeMaskReduction.oracle)
    (fun _ : Unit => (⟨(), .running {outputTape := ResponseLoading.loaded key.toList}, []⟩ : CryptoOracle.Interactive.Configuration Unit))
    (fun _ _ : Unit => loadedFrame key.toList) (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by
      simp [TimedExecution.eval, Reification.timedStep, Reification.terminal,
        Reification.perform, Reification.action, transition, loadCode, loadedFrame,
        Machine.Instruction.next, PMF.pure_map])

private noncomputable def rawLoad (key : Bits width) :=
  ((ResponseLoading.procedure loadCode NativeMaskReduction.oracle).reindex
    (fun _ : Unit => (⟨{}, (), [], key.toList⟩ : ResponseLoading.Input Unit))).seq (halt key)
      (fun _ _ _ => rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

noncomputable def load (key : Bits width) :=
  (rawLoad key).observe (fun _ => ()) (fun _ _ => loadedFrame key.toList) (fun _ _ _ => rfl)

theorem load_budget (key : Bits width) : (load key).budget () = 3 * width + 3 := by
  change (3 * key.toList.length + 2) + 1 = _
  rw [Bits.length_toList]

theorem load_semantics (key : Bits width) : (load key).semantics () = PMF.pure () :=
  PMF.map_const _ _

def loadBoundary : Control → Bool
  | .loading frame => Reification.terminal frame.control
  | _ => true

noncomputable def loading (key : Bits width) :=
  (load key).liftBoundary (fun frame => Reification.terminal frame.control)
    (fun _ _ _ => rfl)
    (fun frame h => by simp [Reification.timedStep, h])
    (fun _ _ => ()) (fun _ output => by cases output; rfl)
    (step distribution message code) loadBoundary Control.loading (fun _ => rfl)
    (fun frame h => by simp [step, h])

theorem aligned (response : List Bool) :
    (ResponseLoading.loaded response).moveLeft.moveRight = retainedKey response := by
  cases response <;> rfl

noncomputable def alignment (key : Bits width) :=
  TimedExecution.Procedure.ofFixed (step distribution message code)
    (fun _ : Unit => .loading (loadedFrame key.toList))
    (fun _ _ : Unit => .active (.producing (NativeMaskReduction.initial key message)))
    (fun _ => PMF.pure ()) (fun _ => 2)
    (fun _ => by
      simp [TimedExecution.eval, step, loadedFrame, Reification.terminal, loaderMachine,
        aligned, NativeMaskReduction.initial, PMF.pure_map])

variable {Output : Type u} (Q : Machine.Procedure Machine.Configuration Output)
    (hEntry : ∀ machine, Q.execution.entry machine = machine.resumeAt 0)
    (hHalt : ∀ machine output, output ∈ (Q.execution.semantics machine).support →
      (Q.execution.exit machine output).halted = true)
    (cap : Nat) (hCap : ∀ ciphertext : List Bool, ciphertext.length = width →
      Q.execution.budget (publicCaller ciphertext) ≤ cap)

noncomputable def body (key : Bits width) :=
  ((loading distribution message Q.code key).seq (alignment distribution message Q.code key)
    (fun _ _ _ => rfl) (fun _ => 2) (fun _ _ _ => Nat.le_refl _)).seq
      (((NativeMaskReduction.whole key message Q hEntry cap hCap).transport
        (step distribution message Q.code) Control.active (fun _ => rfl)).reindex (fun _ : Unit × Unit => ()))
      (fun _ _ _ => rfl) (fun _ => 49 * width + 36 + cap)
      (fun _ _ _ => le_of_eq (NativeMaskReduction.budget key message Q hEntry cap hCap))

theorem body_budget (key : Bits width) :
    (body distribution message Q hEntry cap hCap key).budget () = 52 * width + 41 + cap := by
  change ((load key).budget () + 2) + (49 * width + 36 + cap) = _
  rw [load_budget]
  omega

noncomputable def whole :=
  (query distribution message Q.code).seq
    (TimedExecution.Procedure.dispatch (fun key => body distribution message Q hEntry cap hCap key))
    (fun _ _ _ => rfl) (fun _ => 52 * width + 41 + cap)
    (fun _ key _ => le_of_eq (body_budget distribution message Q hEntry cap hCap key))

theorem budget : (whole distribution message Q hEntry cap hCap).budget () = 52 * width + 42 + cap := by
  change 1 + (52 * width + 41 + cap) = _
  omega

/-- Full physical endpoint distribution, including every saved challenge,
caller history and final native observer configuration. -/
theorem physical_semantics :
    ((whole distribution message Q hEntry cap hCap).semantics ()).map
      ((whole distribution message Q hEntry cap hCap).exit ()) =
      distribution.bind (fun key =>
        (Q.execution.semantics (publicCaller (OneTimePad.encrypt key message).toList)).map
          (fun output => Control.active (NativeContinuation.Control.observing
            (NativeMaskReduction.finish key message)
            (Q.execution.exit (publicCaller (OneTimePad.encrypt key message).toList) output)))) := by
  simp only [whole, TimedExecution.Procedure.seq, query, TimedExecution.Procedure.ofFixed,
    TimedExecution.Procedure.dispatch, body, loading, TimedExecution.Procedure.liftBoundary,
    load_semantics, alignment, TimedExecution.Procedure.reindex, TimedExecution.Procedure.transport,
    NativeMaskReduction.whole_semantics, NativeMaskReduction.whole_exit,
    PMF.map_bind, PMF.bind_map, PMF.bind_bind, PMF.pure_map, PMF.pure_bind, PMF.map_comp, Function.comp_def]
  rfl

include hHalt in
noncomputable def completion :=
  Completion.ofProcedure (whole distribution message Q hEntry cap hCap) rfl
    (terminal := terminal)
    (by
      intro output ho
      have hs : (whole distribution message Q hEntry cap hCap).exit () output ∈
          (((whole distribution message Q hEntry cap hCap).semantics ()).map
            ((whole distribution message Q hEntry cap hCap).exit ())).support := by
        rw [PMF.mem_support_map_iff]
        exact ⟨output, ho, rfl⟩
      rw [physical_semantics, PMF.mem_support_bind_iff] at hs
      obtain ⟨key, _, hs⟩ := hs
      rw [PMF.mem_support_map_iff] at hs
      obtain ⟨native, hn, he⟩ := hs
      rw [← he]
      exact hHalt _ _ hn)

include hHalt in
theorem completion_game :
    ((completion distribution message Q hEntry hHalt cap hCap).execution.semantics ()).map result =
      distribution.bind (fun key => observer Q (OneTimePad.encrypt key message).toList) := by
  rw [completion, Completion.ofProcedure_semantics, physical_semantics]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, result, observer,
    decision, ReusableNativeObservation.decision]

noncomputable def game (horizon : Nat) : PMF Bool :=
  (TimedExecution.eval (step distribution message Q.code) horizon .querying).map result

include hEntry hHalt hCap in
/-- Actual challenge querying, loading, masking and native observation agree
with the distributional reduction. Every ownership transfer is charged. -/
theorem game_eq (horizon : Nat) (hTime : 52 * width + 42 + cap ≤ horizon) :
    game distribution message Q horizon =
      distribution.bind (fun key => observer Q (OneTimePad.encrypt key message).toList) := by
  let C := completion distribution message Q hEntry hHalt cap hCap
  have h := C.final_run (absorbing distribution message Q.code) horizon
    (by change (whole distribution message Q hEntry cap hCap).budget () ≤ horizon; rw [budget]; exact hTime)
  change TimedExecution.eval (step distribution message Q.code) horizon .querying = _ at h
  have hg := congrArg (fun p => p.map result) h
  rw [game]
  simpa only [C, completion, Completion.ofProcedure_semantics, physical_semantics,
    PMF.map_bind, PMF.map_comp, Function.comp_def, result, observer, decision,
    ReusableNativeObservation.decision] using hg

include hEntry hHalt in
/-- Real and ideal challenge distributions both use this same executable
reduction. Only the challenge experiment changes between the two worlds. -/
theorem reduce_game_eq (G : Generator) (n : Nat) (messages : G.Messages n) (side : Bool)
    (distribution : PMF (Bits (G.outputLength n)))
    (cap : Nat) (hCap : ∀ ciphertext : List Bool, ciphertext.length = G.outputLength n →
      Q.execution.budget (publicCaller ciphertext) ≤ cap)
    (horizon : Nat) (hTime : 52 * G.outputLength n + 42 + cap ≤ horizon) :
    game distribution (G.message messages side) Q horizon =
      distribution.bind (G.reduce messages side (fun ciphertext => observer Q ciphertext.toList)) := by
  rw [game_eq distribution (G.message messages side) Q hEntry hHalt cap hCap horizon hTime]
  congr 1
  funext key
  unfold Generator.reduce OneTimePad.encrypt
  rw [Bits.xor_comm]

include hEntry hHalt hCap in
/-- At a completed execution the counter records exactly one external query,
not just an upper bound obtained by assigning tags to controller states. -/
theorem exactly_one_query (horizon : Nat) (hTime : 52 * width + 42 + cap ≤ horizon)
    (target : Control × Nat)
    (h : target ∈ (TimedExecution.eval
      (OneUseCounter.countedStep (step distribution message Q.code) queryEvent) horizon (.querying, 0)).support) :
    target.2 = 1 := by
  have hm : target.1 ∈ (TimedExecution.eval (step distribution message Q.code) horizon .querying).support := by
    rw [← OneUseCounter.marginal (step distribution message Q.code) queryEvent horizon (.querying, 0)]
    rw [PMF.mem_support_map_iff]
    exact ⟨target, h, rfl⟩
  let C := completion distribution message Q hEntry hHalt cap hCap
  have hr := C.final_run (absorbing distribution message Q.code) horizon
    (by change (whole distribution message Q hEntry cap hCap).budget () ≤ horizon; rw [budget]; exact hTime)
  change TimedExecution.eval (step distribution message Q.code) horizon .querying = _ at hr
  rw [hr] at hm
  have ht := C.stopped target.1 hm
  rw [query_counter distribution message Q.code horizon target h]
  cases hx : target.1 with
  | querying => simp [hx, terminal] at ht
  | loading => rfl
  | aligning => rfl
  | active => rfl

theorem time_polynomial {width observerCap : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hObserver : PolynomiallyBounded observerCap) :
    PolynomiallyBounded (fun n => 52 * width n + 42 + observerCap n) :=
  (((PolynomiallyBounded.const 52).mul hWidth).add (PolynomiallyBounded.const 42)).add hObserver

end Foundation.Symmetric.EncryptThenMAC.NativeMaskChallenge
