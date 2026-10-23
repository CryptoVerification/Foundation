import Foundation.Crypto.Semantics.Oracle.StatefulDiagramHigher
import Foundation.Crypto.Semantics.Oracle.StatefulDiagramProofSupport

/-! Materialized higher exchange diagrams and a semantic boundary for the
computed proof obligations. The independent-register example is diagnostic,
not a replacement for the actual MAC caller verified in the previous module. -/
namespace Foundation.Examples.StatefulDiagramAnalysisTransport
open Foundation.Probability CryptoOracle.StatefulDiagram

namespace Checked

def signature (op : Fin 4) : Interface (Fin 5) := ⟨{4}, {op.castSucc}⟩

def left := braidLeft signature 0 1 2 (by decide) (by decide) (by decide)
def right := braidRight signature 0 1 2 (by decide) (by decide) (by decide)
def braid : ExchangeHigher signature left right := .braid 0 1 2 (by decide) (by decide) (by decide)

def distantLeft := farLeft signature 0 1 2 3 (by decide) (by decide)
def distantRight := farRight signature 0 1 2 3 (by decide) (by decide)
def distant : ExchangeHigher signature distantLeft distantRight := .far 0 1 2 3 (by decide) (by decide)

def doubleSwap := swapTwice signature 0 1 (by decide) (by decide)
def cancellation : ExchangeHigher signature doubleSwap (.refl [0, 1]) := .involution 0 1 (by decide) (by decide)

theorem generated_inputs : dependencies signature [0, 1, 2] {0, 2} = ({4} : Finset (Fin 5)) := by
  ext slot
  fin_cases slot <;> simp [dependencies, neededBefore, signature]

theorem generated_required : required signature [0, 1, 2] {0, 2} = ({0, 2} : Finset (Fin 4)) := by
  ext op
  fin_cases op <;> simp [required, dependencies, neededBefore, signature]

theorem generated_obligations : obligations signature [0, 1, 2] {0, 2} {0, 1} = ({0} : Finset (Fin 4)) := by
  rw [obligations, generated_required]
  decide

theorem reordered_obligations : obligations signature [2, 1, 0] {0, 2} {0, 1} = ({0} : Finset (Fin 4)) := by
  rw [← left.obligations_eq signature {0, 2} {0, 1}]
  exact generated_obligations

theorem both_operational_orders {Value : Type} (world : Kernels signature Value) (store : Store (Fin 5) Value) :
    execute signature world [0, 1, 2] store = execute signature world [2, 1, 0] store :=
  left.sound signature world store

theorem repair_after_reorder {Value : Type} (old repaired : Kernels signature Value)
    (same : ∀ op ∉ ({0, 1} : Finset (Fin 4)), old op = repaired op)
    (localLaw : old 0 = repaired 0) (store : Store (Fin 5) Value) :
    (execute signature old [2, 1, 0] store).map (view {0, 2}) =
      (execute signature repaired [2, 1, 0] store).map (view {0, 2}) := by
  apply left.repair_reordered signature {0, 2} {0, 1} old repaired same
  rw [generated_obligations]
  intro op member
  have equal : op = 0 := Finset.mem_singleton.mp member
  subst op
  exact localLaw

/-- info: (3, 3, 2, 2, 2, 1) -/
#guard_msgs in
#eval (left.swapCount signature, right.swapCount signature,
  distantLeft.swapCount signature, distantRight.swapCount signature,
  (required signature [0, 1, 2] {0, 2}).card,
  (obligations signature [2, 1, 0] {0, 2} {0, 1}).card)

def uniformCertificate (old : Kernels signature Bool) :
    ReuseCertificate signature old {0, 2} [0, 1, 2] [2, 1, 0] := .checked left

theorem uniform_support_empty (old : Kernels signature Bool) :
    (uniformCertificate old).support signature old {0, 2} = ∅ := rfl

theorem uniform_check_any_change (old : Kernels signature Bool) (changed : Finset (Fin 4)) :
    (uniformCertificate old).check signature old {0, 2} changed = true := by
  change decide ((uniformCertificate old).support signature old {0, 2} ∩ changed = ∅) = true
  rw [uniform_support_empty]
  simp only [Finset.empty_inter, decide_true]

theorem uniform_reuse_after_any_update (old updated : Kernels signature Bool) (store : Store (Fin 5) Bool) :
    (execute signature updated [0, 1, 2] store).map (view {0, 2}) =
      (execute signature updated [2, 1, 0] store).map (view {0, 2}) := by
  apply (uniformCertificate old).check_sound signature old {0, 2} updated Finset.univ
  · intro op absent
    exact False.elim (absent (Finset.mem_univ _))
  · exact uniform_check_any_change old _

end Checked

namespace SemanticBoundary

/-- Both operations overwrite the same location with the same constant. -/
def signature (_ : Bool) : Interface Bool := ⟨∅, {false}⟩
noncomputable def world : Kernels signature Bool := fun _ _ => PMF.pure fun _ => false

theorem same_full_execution (store : Store Bool Bool) :
    execute signature world [false, true] store = execute signature world [true, false] store := by
  simp only [execute, step, world, signature, PMF.pure_map, PMF.pure_bind]

theorem first_required : required signature [false, true] {false} = ({true} : Finset Bool) := by decide
theorem second_required : required signature [true, false] {false} = ({false} : Finset Bool) := by decide

theorem different_required : required signature [false, true] {false} ≠ required signature [true, false] {false} := by
  rw [first_required, second_required]
  decide

theorem different_obligations : obligations signature [false, true] {false} {false} ≠
    obligations signature [true, false] {false} {false} := by
  simp only [obligations, first_required, second_required]
  decide

/-- Mere equality of game distributions does not make this analysis canonical. -/
theorem semantic_equality_insufficient :
    ¬ (∀ (one two : List Bool),
      (∀ store, execute signature world one store = execute signature world two store) →
      required signature one {false} = required signature two {false}) := by
  intro all
  exact different_required (all [false, true] [true, false] same_full_execution)

/-- Change only operation false. The update that was overwritten in one
order becomes observable after the old semantic reordering. -/
noncomputable def editedWorld : Kernels signature Bool := fun op _ => PMF.pure fun _ => !op

theorem original_order_observation (store : Store Bool Bool) :
    (execute signature editedWorld [false, true] store).map (fun final => final false) = PMF.pure false := by
  simp [execute, step, editedWorld, signature, PMF.pure_map, write]

theorem reversed_order_observation (store : Store Bool Bool) :
    (execute signature editedWorld [true, false] store).map (fun final => final false) = PMF.pure true := by
  simp [execute, step, editedWorld, signature, PMF.pure_map, write]

theorem edit_breaks_semantic_reorder (store : Store Bool Bool) :
    execute signature editedWorld [false, true] store ≠ execute signature editedWorld [true, false] store := by
  intro equal
  have observed := congrArg (fun (law : PMF (Store Bool Bool)) => law.map (fun final => final false)) equal
  rw [original_order_observation, reversed_order_observation] at observed
  have impossible := congrArg (fun (law : PMF Bool) => law false) observed
  simp at impossible

/-- Old-world equality alone is not a certificate stable under kernel edits. -/
theorem old_equivalence_not_edit_stable :
    (∀ store, execute signature world [false, true] store = execute signature world [true, false] store) ∧
    (∀ store, execute signature editedWorld [false, true] store ≠ execute signature editedWorld [true, false] store) :=
  ⟨same_full_execution, edit_breaks_semantic_reorder⟩

theorem exchange_rejected : checkExchange signature false true = false := by decide

/-- info: (false, 1, 1, 0, 1) -/
#guard_msgs in
#eval (checkExchange signature false true,
  (required signature [false, true] {false}).card, (required signature [true, false] {false}).card,
  (obligations signature [false, true] {false} {false}).card,
  (obligations signature [true, false] {false} {false}).card)

def importedCertificate : ReuseCertificate signature world {false} [false, true] [true, false] where
  plan := .imported [false, true] [true, false]
  valid := fun store => congrArg (PMF.map (view {false})) (same_full_execution store)

theorem imported_support : importedCertificate.support signature world {false} = ({false, true} : Finset Bool) := by
  simp only [importedCertificate, ReuseCertificate.support, ReusePlan.support, equivalenceSupport, first_required, second_required]
  decide

theorem proof_recheck_needed : importedCertificate.fresh signature world {false} {false} = ({false} : Finset Bool) := by
  change importedCertificate.support signature world {false} ∩ {false} = _
  rw [imported_support]
  decide

theorem proof_checker_rejects : importedCertificate.check signature world {false} {false} = false := by
  change decide (importedCertificate.fresh signature world {false} {false} = ∅) = false
  rw [proof_recheck_needed]
  decide

/-- Dataflow-only reuse accepts the SOURCE marginal, but cannot justify the
old semantic reordering. The proof-support checker detects that distinction. -/
theorem source_only_check_accepts : checkReuse signature [false, true] {false} {false} = true := by decide

theorem edited_unchanged (op : Bool) (untouched : op ∉ ({false} : Finset Bool)) : world op = editedWorld op := by
  cases op with
  | false => simp at untouched
  | true => rfl

theorem source_marginal_preserved (store : Store Bool Bool) :
    (execute signature world [false, true] store).map (view {false}) =
      (execute signature editedWorld [false, true] store).map (view {false}) :=
  checkReuse_sound signature world editedWorld [false, true] {false} {false} store edited_unchanged source_only_check_accepts

/-- info: (true, false, 1) -/
#guard_msgs in
#eval (checkReuse signature [false, true] {false} {false},
  importedCertificate.plan.check signature {false} {false},
  (importedCertificate.plan.fresh signature {false} {false}).card)

end SemanticBoundary
end Foundation.Examples.StatefulDiagramAnalysisTransport
