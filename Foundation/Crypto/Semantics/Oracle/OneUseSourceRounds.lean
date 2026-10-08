import Foundation.Crypto.Semantics.Oracle.OneUseBoundaryContracts
import Foundation.Crypto.Semantics.Oracle.RequestLayout

/-! State-dependent rounds of arbitrary finite caller code. A round executes
ordinary instructions, then a physically certified query, and returns the
whole caller frame with its updated use flag. Missing query layout is a
zero-step return, never a claimed halt; whole execution needs a separate
supported-final-state stopping certificate. -/
namespace CryptoOracle.Interactive.OneUseSourceRounds
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

structure Boundary (State : Type u) where
  spent : Bool
  frame : Configuration State

def embed (store : Machine.Tape) (source : Boundary State) : OneUseSource.Control State :=
  .source source.spent store source.frame

def view : OneUseSource.Control State → Boundary State
  | .source spent _ frame => ⟨spent, frame⟩
  | .handling spent saved state trace _ _ => ⟨spent, ⟨state, .running saved, trace⟩⟩

/-- Exact physical layout evidence at a running call instruction. -/
structure CallLayout (code : Code) (frame : Configuration State) where
  machine : Machine.Configuration
  request : List Bool
  tail : List (Option Bool)
  control : frame.control = .running machine
  active : machine.halted = false
  call : code[machine.pc]? = some .call
  tape : machine.outputTape = RequestExport.packetTape [] tail request

theorem CallLayout.unique {code : Code} {frame : Configuration State}
    (first second : CallLayout code frame) : first = second := by
  have hm : first.machine = second.machine := Control.running.inj (first.control.symm.trans second.control)
  have ht : RequestExport.packetTape [] first.tail first.request =
      RequestExport.packetTape [] second.tail second.request :=
    first.tape.symm.trans ((congrArg Machine.Configuration.outputTape hm).trans second.tape)
  obtain ⟨hr, hs⟩ := RequestExport.packetTape_injective ht
  cases first
  cases second
  simp only at hm hr hs
  cases hm
  cases hr
  cases hs
  rfl

variable (code : Code) (oracle : BitOracle State) (key : List Bool) (keyTail : List (Option Bool))

noncomputable def queryAt (source : Boundary State) :
    Procedure (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
      Unit (Boundary State) := by
  classical
  exact if h : Nonempty (CallLayout code source.frame) then
    let data := Classical.choice h
    (OneUseXorRequest.invocation code oracle data.machine source.frame.state source.frame.reverseTrace
      key data.request keyTail data.tail data.active data.call data.tape source.spent).observe view
      (fun _ result => embed (Machine.PairPreparation.operand [] key keyTail) result)
      (by
        intro _ result hs
        rw [OneUseXorRequest.semantics, PMF.mem_support_pure_iff] at hs
        subst result
        cases source.spent <;> simp only [OneUseXorRequest.invocation, Bool.false_eq_true, ↓reduceIte]
        · split <;> rfl
        · rfl)
  else
    Procedure.ofFixed _
      (fun _ => embed (Machine.PairPreparation.operand [] key keyTail) source)
      (fun _ result => embed (Machine.PairPreparation.operand [] key keyTail) result)
      (fun _ => PMF.pure source) (fun _ => 0)
      (fun _ => by simp [TimedExecution.eval, PMF.pure_map])

theorem queryAt_entry (source : Boundary State) :
    (queryAt code oracle key keyTail source).entry () =
      embed (Machine.PairPreparation.operand [] key keyTail) source := by
  classical
  unfold queryAt
  split
  · rename_i h
    simp only [Procedure.observe]
    rw [OneUseXorRequest.entry]
    have hc := (Classical.choice h).control
    rcases source with ⟨spent, state, control, trace⟩
    simp only [embed] at *
    exact congrArg (fun control => OneUseSource.Control.source spent
      (Machine.PairPreparation.operand [] key keyTail) ⟨state, control, trace⟩) hc.symm
  · rfl

theorem queryAt_exit (source result : Boundary State) :
    (queryAt code oracle key keyTail source).exit () result =
      embed (Machine.PairPreparation.operand [] key keyTail) result := by
  classical
  unfold queryAt
  split <;> rfl

/-- A supplied layout gives the same response regardless of which proof
witness was selected. Request and suffix are unique at the physical head. -/
theorem queryAt_semantics (source : Boundary State) (data : CallLayout code source.frame) :
    (queryAt code oracle key keyTail source).semantics () =
      PMF.pure (Boundary.mk (OneUseXorRequest.used source.spent key data.request)
        (NativeCallback.resumed data.machine.advance source.frame.state source.frame.reverseTrace
          data.request (OneUseXorRequest.reply source.spent key data.request))) := by
  classical
  have h : Nonempty (CallLayout code source.frame) := ⟨data⟩
  rw [queryAt, dif_pos h]
  simp only [Procedure.observe]
  rw [OneUseXorRequest.semantics, PMF.pure_map]
  rw [CallLayout.unique (Classical.choice h) data]
  rfl

theorem queryAt_budget (source : Boundary State) (data : CallLayout code source.frame) :
    (queryAt code oracle key keyTail source).budget () =
      OneUseXorRequest.budget source.spent key data.request := by
  classical
  have h : Nonempty (CallLayout code source.frame) := ⟨data⟩
  rw [queryAt, dif_pos h]
  simp only [Procedure.observe]
  rw [OneUseXorRequest.invocation_budget, CallLayout.unique (Classical.choice h) data]

/-- Lack of a layout proof inserts no response, native operation, or halt. -/
theorem queryAt_no_layout (source : Boundary State) (h : ¬ Nonempty (CallLayout code source.frame)) :
    (queryAt code oracle key keyTail source).costed () = PMF.pure (source, 0) := by
  classical
  simp [queryAt, h, Procedure.ofFixed, PMF.pure_map]

theorem queryAt_budget_bound (source : Boundary State) (requestCap : Nat)
    (hRequest : ∀ data : CallLayout code source.frame, data.request.length ≤ requestCap) :
    (queryAt code oracle key keyTail source).budget () ≤ 33 * (key.length + requestCap) + 33 := by
  classical
  by_cases h : Nonempty (CallLayout code source.frame)
  · rw [queryAt_budget code oracle key keyTail source (Classical.choice h)]
    have hQuery := OneUseXorRequest.budget_le key (Classical.choice h).request source.spent
    have hSize := hRequest (Classical.choice h)
    omega
  · simp [queryAt, h, Procedure.ofFixed]

noncomputable def query := Procedure.dispatch (queryAt code oracle key keyTail)

/-- Ordinary instructions retain the use flag; query returns may update it.
No previous response or caller tape is removed from the logical boundary. -/
noncomputable def callerAt (fuel : Nat) (source : Boundary State) :=
  ((OneUseSourceInterval.interval Machine.OneTimePad.Prepared.listProcedure.code code oracle
    source.spent (Machine.PairPreparation.operand [] key keyTail) fuel).reindex
      (fun _ : Unit => source.frame)).observe (fun frame => Boundary.mk source.spent frame)
    (fun _ result => embed (Machine.PairPreparation.operand [] key keyTail) result) (fun _ _ _ => rfl)

noncomputable def caller (fuel : Nat) := Procedure.dispatch (callerAt code oracle key keyTail fuel)

/-- The cap bounds query processing only on actual interval returns. It can
vary with the initial boundary; a later invariant supplies a uniform cap. -/
noncomputable def round (fuel : Nat) (cap : Boundary State → Nat)
    (hCap : ∀ source result, result ∈ ((caller code oracle key keyTail fuel).semantics source).support →
      (query code oracle key keyTail).budget result ≤ cap source) :=
  ((caller code oracle key keyTail fuel).seq (query code oracle key keyTail)
    (fun _ middle _ => queryAt_entry code oracle key keyTail middle) cap hCap).observe Prod.snd
    (fun _ result => embed (Machine.PairPreparation.operand [] key keyTail) result)
    (fun _ result _ => (queryAt_exit code oracle key keyTail result.1 result.2).symm)

theorem round_entry (fuel : Nat) (cap : Boundary State → Nat) (hCap) (source : Boundary State) :
    (round code oracle key keyTail fuel cap hCap).entry source =
      embed (Machine.PairPreparation.operand [] key keyTail) source := rfl

theorem round_exit (fuel : Nat) (cap : Boundary State → Nat) (hCap) (source result : Boundary State) :
    (round code oracle key keyTail fuel cap hCap).exit source result =
      embed (Machine.PairPreparation.operand [] key keyTail) result := rfl

theorem round_budget (fuel : Nat) (cap : Boundary State → Nat) (hCap) (source : Boundary State) :
    (round code oracle key keyTail fuel cap hCap).budget source = fuel + cap source := rfl

theorem round_semantics (fuel : Nat) (cap : Boundary State → Nat) (hCap) (source : Boundary State) :
    (round code oracle key keyTail fuel cap hCap).semantics source =
      ((caller code oracle key keyTail fuel).semantics source).bind
        (query code oracle key keyTail).semantics := by
  simp only [round, Procedure.observe, Procedure.seq, PMF.map_bind, PMF.map_comp, Function.comp_def]
  congr 1
  funext output
  exact PMF.map_id _

/-- A logical terminal witness refers to the original caller's real halt. -/
theorem absorbing (source : Boundary State) (hTerminal : Reification.terminal source.frame.control = true) :
    OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle
      (embed (Machine.PairPreparation.operand [] key keyTail) source) =
      PMF.pure (embed (Machine.PairPreparation.operand [] key keyTail) source) := by
  cases hc : source.frame.control <;>
    simp_all [embed, OneUseSource.step, Reification.timedStep, Reification.terminal, PMF.pure_map]

variable (fuel : Nat) (cap : Boundary State → Nat)
    (hCap : ∀ source result, result ∈ ((caller code oracle key keyTail fuel).semantics source).support →
      (query code oracle key keyTail).budget result ≤ cap source)
    (predicate : Boundary State → Prop)
    (hClosed : ∀ source, predicate source →
      ∀ result ∈ ((round code oracle key keyTail fuel cap hCap).semantics source).support, predicate result)
    (bound : Nat) (hBound : ∀ source, predicate source → fuel + cap source ≤ bound)

/-- Whole finite-round execution on certified layouts. The caller code and
private native program remain the existing finite syntax. Only proof-level
contracts, not an expanded adaptive tree, are composed by this definition. -/
noncomputable def execution (count : Nat) :=
  (round code oracle key keyTail fuel cap hCap).invariantIteration predicate hClosed bound
    (fun source hs => by rw [round_budget]; exact hBound source hs)
    (fun source _ result _ => by rw [round_exit, round_entry]) count

theorem execution_entry (count : Nat) (source : {source // predicate source}) :
    (execution code oracle key keyTail fuel cap hCap predicate hClosed bound hBound count).entry source =
      embed (Machine.PairPreparation.operand [] key keyTail) source.val := by
  unfold execution Procedure.invariantIteration
  rw [Procedure.iterate_entry]
  rfl

theorem execution_exit (count : Nat) (source result : {source // predicate source}) :
    (execution code oracle key keyTail fuel cap hCap predicate hClosed bound hBound count).exit source result =
      embed (Machine.PairPreparation.operand [] key keyTail) result.val := by
  unfold execution Procedure.invariantIteration
  rw [Procedure.iterate_exit]
  rfl

theorem execution_semantics (count : Nat) (source : {source // predicate source}) :
    ((execution code oracle key keyTail fuel cap hCap predicate hClosed bound hBound count).semantics source).map
      Subtype.val = TimedExecution.eval (round code oracle key keyTail fuel cap hCap).semantics count source.val :=
  Procedure.invariantIteration_semantics _ _ _ _ _ _ count source

theorem execution_budget (count : Nat) (source : {source // predicate source}) :
    (execution code oracle key keyTail fuel cap hCap predicate hClosed bound hBound count).budget source =
      count * bound := Procedure.iterate_budget _ _ _ _ count source

include hClosed hBound in
/-- Stop evidence and resource evidence are distinct. All supported logical
final states must be actual caller terminals before a whole physical run is
identified with the logical result distribution at the multiplied budget. -/
theorem run (count : Nat) (source : {source // predicate source})
    (hStops : ∀ final ∈ (TimedExecution.eval (round code oracle key keyTail fuel cap hCap).semantics
      count source.val).support, Reification.terminal final.frame.control = true)
    (horizon : Nat) (hBudget : count * bound ≤ horizon) :
    TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
      horizon (embed (Machine.PairPreparation.operand [] key keyTail) source.val) =
      (TimedExecution.eval (round code oracle key keyTail fuel cap hCap).semantics count source.val).map
        (embed (Machine.PairPreparation.operand [] key keyTail)) := by
  have h := Procedure.invariantIteration_final (round code oracle key keyTail fuel cap hCap)
    predicate hClosed bound (fun source hs => by rw [round_budget]; exact hBound source hs)
    (fun source _ result _ => by rw [round_exit, round_entry]) count source
    (fun final hs => by
      rw [round_entry]
      exact absorbing code oracle key keyTail final (hStops final hs)) horizon hBudget
  have hEntry : (round code oracle key keyTail fuel cap hCap).entry =
      embed (Machine.PairPreparation.operand [] key keyTail) :=
    funext (round_entry code oracle key keyTail fuel cap hCap)
  simpa only [hEntry] using h

end CryptoOracle.Interactive.OneUseSourceRounds
