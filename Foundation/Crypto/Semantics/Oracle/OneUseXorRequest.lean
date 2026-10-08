import Foundation.Crypto.Semantics.Oracle.OneUseXorInvocation
import Foundation.Crypto.Semantics.ProcedurePhysical
import Foundation.Crypto.Semantics.ProcedureStage
import Foundation.Crypto.Semantics.Oracle.ControllerResourceSimulation

/-! A common physical call contract for arbitrary raw requests. Length
validation, success and spent-key rejection are selected by proofs only;
the executed controller performs its existing physical checks. Invalid
fresh requests preserve the unused key. Tape suffixes remain unrestricted. -/
namespace CryptoOracle.Interactive.OneUseXorRequest
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

def reply (spent : Bool) (key request : List Bool) : List Bool :=
  if spent then [false]
  else if key.length = request.length then true :: Machine.OneTimePad.xorList key request
  else [false]

def used (spent : Bool) (key request : List Bool) : Bool :=
  spent || decide (key.length = request.length)

variable (code : Code) (oracle : BitOracle State) (machine : Machine.Configuration)
    (state : State) (trace : List (List Bool × List Bool))
    (key request : List Bool) (keyTail requestTail : List (Option Bool))
    (hActive : machine.halted = false) (hCall : code[machine.pc]? = some .call)
    (hTape : machine.outputTape = RequestExport.packetTape [] requestTail request)

def result (spent : Bool) : OneUseSource.Control State :=
  .source (used spent key request) (Machine.PairPreparation.operand [] key keyTail)
    (NativeCallback.resumed machine.advance state trace request (reply spent key request))

noncomputable def invocation (spent : Bool) :
    Procedure (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
      Unit (OneUseSource.Control State) :=
  if spent then
    (OneUseSource.spentInvocation Machine.OneTimePad.Prepared.listProcedure.code code oracle
      (Machine.PairPreparation.operand [] key keyTail) machine state trace request [] requestTail
      hActive hCall hTape).physical
  else if h : key.length = request.length then
    (OneUseXorInvocation.invocation code oracle machine state trace
      ⟨key, request, keyTail, requestTail, h⟩ hActive hCall hTape).physical
  else
    (OneUseSource.rejectedInvocation Machine.OneTimePad.Prepared.listProcedure.code code oracle
      machine state trace hActive hCall ⟨key, request, keyTail, requestTail, h⟩ hTape).physical

theorem entry (spent : Bool) :
    (invocation code oracle machine state trace key request keyTail requestTail hActive hCall hTape spent).entry () =
      .source spent (Machine.PairPreparation.operand [] key keyTail) ⟨state, .running machine, trace⟩ := by
  cases spent <;> simp only [invocation, Bool.false_eq_true, ↓reduceIte]
  · split <;> rfl
  · rfl

def budget (spent : Bool) (key request : List Bool) : Nat :=
  if spent then 2 * request.length + 22
  else if key.length = request.length then 33 * key.length + 33
  else 2 * request.length + 12 * min key.length request.length + 29

theorem invocation_budget (spent : Bool) :
    (invocation code oracle machine state trace key request keyTail requestTail hActive hCall hTape spent).budget () =
      budget spent key request := by
  cases spent <;> simp only [invocation, budget, Bool.false_eq_true, ↓reduceIte, Procedure.physical_budget]
  · split
    · rw [Procedure.physical_budget, OneUseXorInvocation.budget]
    · rw [Procedure.physical_budget, OneUseSource.rejectedInvocation_budget]; rfl
  · rw [OneUseSource.spentInvocation_budget]

theorem semantics (spent : Bool) :
    (invocation code oracle machine state trace key request keyTail requestTail hActive hCall hTape spent).semantics () =
      PMF.pure (result machine state trace key request keyTail spent) := by
  cases spent <;> simp only [invocation, Bool.false_eq_true, ↓reduceIte, Procedure.physical_semantics]
  · split
    · rw [Procedure.physical_semantics, OneUseXorInvocation.distribution]
      simp_all [result, reply, used]
    · rw [Procedure.physical_semantics, OneUseSource.rejectedInvocation_distribution]
      simp_all [result, reply, used]
  · rw [OneUseSource.spentInvocation_distribution]
    rfl

/-- A budget bounds a return, without asserting that the caller halts.
The joint physical-state/time distribution continues the original VM. -/
theorem resume (spent : Bool) (horizon : Nat) (hBudget : budget spent key request ≤ horizon) :
    TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
      horizon (.source spent (Machine.PairPreparation.operand [] key keyTail) ⟨state, .running machine, trace⟩) =
      ((invocation code oracle machine state trace key request keyTail requestTail hActive hCall hTape spent).costed ()).bind
        (fun returned => TimedExecution.eval
          (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
          (horizon - returned.2) returned.1) := by
  have h := (invocation code oracle machine state trace key request keyTail requestTail hActive hCall hTape spent).law
    () horizon (by rw [invocation_budget]; exact hBudget)
  rw [entry] at h
  cases spent <;> simp only [invocation, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · by_cases heq : key.length = request.length
    · simp only [heq, ↓reduceDIte] at h ⊢; exact h
    · simp only [heq, ↓reduceDIte] at h ⊢; exact h
  · exact h

/-- The same actual call can enter the common finite-stage composition
rules. The proof-level conversion does not replace the controller code. -/
noncomputable def stage (spent : Bool) :=
  (invocation code oracle machine state trace key request keyTail requestTail hActive hCall hTape spent).toStage ()

theorem stage_distribution (spent : Bool) :
    (stage code oracle machine state trace key request keyTail requestTail hActive hCall hTape spent).outcome.map Prod.fst =
      PMF.pure (result machine state trace key request keyTail spent) := by
  rw [stage, Procedure.toStage_distribution, semantics, PMF.pure_map]
  cases spent <;> simp only [invocation, Bool.false_eq_true, ↓reduceIte]
  · split <;> rfl
  · rfl

/-- All three request branches share the same bound on retained physical
memory, including request validation, rejection recovery and delivery. -/
theorem memory_peak (spent : Bool) (stateSize : State → Nat) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request answer, answer ∈ (oracle state request).support →
      stateSize answer.1 ≤ stateSize state + stateIncrement ∧ answer.2.length ≤ responseCap)
    (elapsed : Nat) (hElapsed : elapsed ≤ budget spent key request)
    (target : OneUseSource.Control State)
    (h : target ∈ (TimedExecution.eval
      (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle) elapsed
      (.source spent (Machine.PairPreparation.operand [] key keyTail) ⟨state, .running machine, trace⟩)).support) :
    ControllerStorage.sourceCells stateSize target ≤
      4 * (ControllerExtent.sourceExtent stateSize
        (.source spent (Machine.PairPreparation.operand [] key keyTail) ⟨state, .running machine, trace⟩) +
          budget spent key request * (stateIncrement + responseCap + 2)) ^ 2 +
      11 * (ControllerExtent.sourceExtent stateSize
        (.source spent (Machine.PairPreparation.operand [] key keyTail) ⟨state, .running machine, trace⟩) +
          budget spent key request * (stateIncrement + responseCap + 2)) + 2 :=
  (ControllerExtent.sourceEnvelope stateSize Machine.OneTimePad.Prepared.listProcedure.code code oracle
    stateIncrement responseCap hOracle).peak _ elapsed hElapsed _ target h

/-- One uniform call cap covers fresh, invalid and spent requests. -/
theorem budget_le (spent : Bool) : budget spent key request ≤ 33 * (key.length + request.length) + 33 := by
  cases spent <;> simp only [budget, Bool.false_eq_true, ↓reduceIte]
  · split
    · omega
    · have := Nat.min_le_left key.length request.length; omega
  · omega

end CryptoOracle.Interactive.OneUseXorRequest
