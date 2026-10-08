import Foundation.Crypto.Semantics.Oracle.OneUseSourceRounds
import Foundation.Crypto.Semantics.Oracle.OneUseProgramContract

/-! Package layout closure, bounds and genuine stopping of finite caller
rounds into the consumer interface used by physical key initialization. -/
namespace CryptoOracle.Interactive.OneUseSourceRounds
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

structure Certificate (code : Code) (oracle : BitOracle State) (key : List Bool)
    (keyTail : List (Option Bool)) (callerFrame : Configuration State) where
  fuel : Nat
  cap : Boundary State → Nat
  capProof : ∀ source result, result ∈ ((caller code oracle key keyTail fuel).semantics source).support →
    (query code oracle key keyTail).budget result ≤ cap source
  predicate : Boundary State → Prop
  closed : ∀ source, predicate source →
    ∀ result ∈ ((round code oracle key keyTail fuel cap capProof).semantics source).support, predicate result
  bound : Nat
  bounded : ∀ source, predicate source → fuel + cap source ≤ bound
  count : Nat
  initial : predicate ⟨false, callerFrame⟩
  stops : ∀ final ∈ (TimedExecution.eval (round code oracle key keyTail fuel cap capProof).semantics
    count ⟨false, callerFrame⟩).support, Reification.terminal final.frame.control = true

namespace Certificate
variable {code : Code} {oracle : BitOracle State} {key : List Bool}
    {keyTail : List (Option Bool)} {callerFrame : Configuration State}
    (C : Certificate code oracle key keyTail callerFrame)

def start : {source // C.predicate source} := ⟨⟨false, callerFrame⟩, C.initial⟩

noncomputable def procedure :=
  (execution code oracle key keyTail C.fuel C.cap C.capProof C.predicate C.closed C.bound C.bounded C.count).reindex
    (fun _ : Unit => C.start)

/-- The whole returned physical state/time law is passed directly to the
initializer. Proof data and the logical use flag add no runtime transitions. -/
noncomputable def consumer : OneUseProgramContract.Consumer Machine.OneTimePad.Prepared.listProcedure.code
    code oracle callerFrame (Machine.PairPreparation.operand [] key keyTail) where
  execution := C.procedure.physical
  entry := by
    change (execution code oracle key keyTail C.fuel C.cap C.capProof C.predicate C.closed C.bound C.bounded C.count).entry
      C.start = _
    rw [execution_entry]
    rfl
  exit := fun _ => rfl
  stops := by
    intro physical hs
    change physical ∈ (((execution code oracle key keyTail C.fuel C.cap C.capProof C.predicate C.closed C.bound C.bounded C.count).semantics
      C.start).map ((execution code oracle key keyTail C.fuel C.cap C.capProof C.predicate C.closed C.bound C.bounded C.count).exit C.start)).support at hs
    rw [PMF.mem_support_map_iff] at hs
    obtain ⟨final, hFinal, he⟩ := hs
    subst physical
    rw [execution_exit]
    change Reification.terminal final.val.frame.control = true
    apply C.stops final.val
    change final.val ∈ (TimedExecution.eval (round code oracle key keyTail C.fuel C.cap C.capProof).semantics C.count C.start.val).support
    rw [← execution_semantics code oracle key keyTail C.fuel C.cap C.capProof C.predicate C.closed C.bound C.bounded C.count C.start,
      PMF.mem_support_map_iff]
    exact ⟨final, hFinal, rfl⟩

theorem consumer_budget : C.consumer.execution.budget () = C.count * C.bound := by
  change C.procedure.budget () = _
  exact execution_budget code oracle key keyTail C.fuel C.cap C.capProof C.predicate C.closed C.bound C.bounded C.count C.start

/-- Initialization can use the logical final distribution without inspecting
an expanded proof tree or replacing the actual stored private key. -/
theorem consumer_semantics : C.consumer.execution.semantics () =
    (TimedExecution.eval (round code oracle key keyTail C.fuel C.cap C.capProof).semantics C.count
      (Boundary.mk false callerFrame)).map (embed (Machine.PairPreparation.operand [] key keyTail)) := by
  change ((execution code oracle key keyTail C.fuel C.cap C.capProof C.predicate C.closed C.bound C.bounded C.count).semantics C.start).map
    ((execution code oracle key keyTail C.fuel C.cap C.capProof C.predicate C.closed C.bound C.bounded C.count).exit C.start) = _
  have hExit : (execution code oracle key keyTail C.fuel C.cap C.capProof C.predicate C.closed C.bound C.bounded C.count).exit C.start =
      embed (Machine.PairPreparation.operand [] key keyTail) ∘ Subtype.val := by
    funext output
    exact execution_exit code oracle key keyTail C.fuel C.cap C.capProof C.predicate C.closed C.bound C.bounded C.count C.start output
  rw [hExit, ← PMF.map_comp, execution_semantics]
  rfl

end Certificate
end CryptoOracle.Interactive.OneUseSourceRounds
