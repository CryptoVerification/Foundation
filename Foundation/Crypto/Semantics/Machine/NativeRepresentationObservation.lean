import Foundation.Crypto.Semantics.Machine.RepresentationLayout
import Foundation.Crypto.Semantics.Machine.NativeFirstArrival
import Foundation.Crypto.Semantics.ProcedureCostObservation
import Foundation.Crypto.Semantics.Probability.ObserverBound

/-! Observe complete finite representations without an invariant-observer
restriction. Cell content, represented layout, and time are retained jointly.
Reconstruction is an identity on supported physical exits; no normalization,
encoding cost, or observer efficiency is inferred from the factorization. -/
namespace Machine.NativeComponent
open Foundation.Probability
open scoped ENNReal
universe u v w x
set_option backward.isDefEq.respectTransparency false
variable {Input : Type u} {Output : Type v} {Value : Type w} {Observed : Type x}
    (P : NativeComponent Input Output)

theorem representation_observation (view : Input → Output → Value) (cells : Value → Configuration)
    (equivalent : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      (P.procedure.execution.exit input output).Equivalent (cells (view input output)))
    (kernel : Configuration × Nat → PMF Observed) (input : Input) :
    (P.procedure.execution.costed input).bind
      (fun result => kernel (P.procedure.execution.exit input result.1, result.2)) =
    ((P.procedure.execution.costed input).map (fun result =>
      ((view input result.1, (P.procedure.execution.exit input result.1).layout), result.2))).bind
      (fun result => kernel (Configuration.reconstruct result.1.2 (cells result.1.1), result.2)) := by
  rw [PMF.bind_map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  dsimp only [Function.comp_def]
  rw [Configuration.reconstruct_eq_of_equivalent _ _
    (equivalent input result.1 (P.procedure.execution.result_support input result hResult))]

theorem representation_eq_of_joint_eq (view : Input → Output → Value) (cells : Value → Configuration)
    (equivalent : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      (P.procedure.execution.exit input output).Equivalent (cells (view input output)))
    (left right : Input)
    (sameJoint : (P.procedure.execution.costed left).map (fun result =>
      ((view left result.1, (P.procedure.execution.exit left result.1).layout), result.2)) =
      (P.procedure.execution.costed right).map (fun result =>
        ((view right result.1, (P.procedure.execution.exit right result.1).layout), result.2)))
    (kernel : Configuration × Nat → PMF Observed) :
    (P.procedure.execution.costed left).bind
      (fun result => kernel (P.procedure.execution.exit left result.1, result.2)) =
    (P.procedure.execution.costed right).bind
      (fun result => kernel (P.procedure.execution.exit right result.1, result.2)) := by
  rw [P.representation_observation view cells equivalent kernel left,
    P.representation_observation view cells equivalent kernel right, sameJoint]

theorem representation_bound (view : Input → Output → Value) (cells : Value → Configuration)
    (equivalent : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      (P.procedure.execution.exit input output).Equivalent (cells (view input output)))
    (left right : Input) (allowed : (((Value × Configuration.Layout) × Nat) → PMF Bool) → Prop)
    (epsilon : ℝ≥0∞)
    (bound : ObserverBound allowed
      ((P.procedure.execution.costed left).map (fun result =>
        ((view left result.1, (P.procedure.execution.exit left result.1).layout), result.2)))
      ((P.procedure.execution.costed right).map (fun result =>
        ((view right result.1, (P.procedure.execution.exit right result.1).layout), result.2))) epsilon)
    (kernel : Configuration × Nat → PMF Bool)
    (admitted : allowed (fun result => kernel (Configuration.reconstruct result.1.2 (cells result.1.1), result.2))) :
    probabilityGap
      (eventProb ((P.procedure.execution.costed left).bind
        (fun result => kernel (P.procedure.execution.exit left result.1, result.2))) (· = true))
      (eventProb ((P.procedure.execution.costed right).bind
        (fun result => kernel (P.procedure.execution.exit right result.1, result.2))) (· = true)) ≤ epsilon := by
  rw [P.representation_observation view cells equivalent kernel left,
    P.representation_observation view cells equivalent kernel right]
  exact bound _ admitted

theorem representation_joint_of_fixed_layout_time (view : Input → Output → Value)
    (input : Input) (shape : Configuration.Layout) (duration : Nat)
    (sameLayout : ∀ result, result ∈ (P.procedure.execution.costed input).support →
      (P.procedure.execution.exit input result.1).layout = shape)
    (fixed : ∀ result, result ∈ (P.procedure.execution.costed input).support → result.2 = duration) :
    (P.procedure.execution.costed input).map (fun result =>
      ((view input result.1, (P.procedure.execution.exit input result.1).layout), result.2)) =
    ((P.procedure.execution.semantics input).map (view input)).map
      (fun value => ((value, shape), duration)) := by
  calc
    _ = (P.procedure.execution.costed input).map (fun result => ((view input result.1, shape), result.2)) := by
      rw [PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext result hResult
      change PMF.pure ((view input result.1, (P.procedure.execution.exit input result.1).layout), result.2) = _
      rw [sameLayout result hResult]
      rfl
    _ = _ := by
      rw [P.procedure.execution.costed_view_of_fixed_time (fun input output => (view input output, shape)) input duration fixed,
        PMF.map_comp, PMF.map_comp]
      rfl

theorem representation_joint_of_layout_view (view : Input → Output → Value)
    (shape : Value → Configuration.Layout) (input : Input)
    (sameLayout : ∀ result, result ∈ (P.procedure.execution.costed input).support →
      (P.procedure.execution.exit input result.1).layout = shape (view input result.1)) :
    (P.procedure.execution.costed input).map (fun result =>
      ((view input result.1, (P.procedure.execution.exit input result.1).layout), result.2)) =
      ((P.procedure.execution.costed input).map (fun result => (view input result.1, result.2))).map
        (fun result => ((result.1, shape result.1), result.2)) := by
  rw [PMF.map_comp, PMF.map, PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  change PMF.pure ((view input result.1, (P.procedure.execution.exit input result.1).layout), result.2) = _
  rw [sameLayout result hResult]
  rfl

theorem representation_eq_of_public_layout (view : Input → Output → Value) (cells : Value → Configuration)
    (equivalent : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      (P.procedure.execution.exit input output).Equivalent (cells (view input output)))
    (shape : Value → Configuration.Layout) (left right : Input)
    (leftLayout : ∀ result, result ∈ (P.procedure.execution.costed left).support →
      (P.procedure.execution.exit left result.1).layout = shape (view left result.1))
    (rightLayout : ∀ result, result ∈ (P.procedure.execution.costed right).support →
      (P.procedure.execution.exit right result.1).layout = shape (view right result.1))
    (sameJoint : (P.procedure.execution.costed left).map (fun result => (view left result.1, result.2)) =
      (P.procedure.execution.costed right).map (fun result => (view right result.1, result.2)))
    (kernel : Configuration × Nat → PMF Observed) :
    (P.procedure.execution.costed left).bind
      (fun result => kernel (P.procedure.execution.exit left result.1, result.2)) =
    (P.procedure.execution.costed right).bind
      (fun result => kernel (P.procedure.execution.exit right result.1, result.2)) := by
  apply P.representation_eq_of_joint_eq view cells equivalent left right _ kernel
  rw [P.representation_joint_of_layout_view view shape left leftLayout,
    P.representation_joint_of_layout_view view shape right rightLayout, sameJoint]

theorem representation_encoded_joint (view : Input → Output → Value) (cells : Value → Configuration)
    (equivalent : ∀ input output, output ∈ (P.procedure.execution.semantics input).support →
      (P.procedure.execution.exit input output).Equivalent (cells (view input output))) (input : Input) :
    (P.procedure.execution.costed input).map (fun result =>
      (NativeEncodedResources.completeEncoding.encode (P.procedure.code, P.procedure.execution.exit input result.1), result.2)) =
      ((P.procedure.execution.costed input).map (fun result =>
        ((view input result.1, (P.procedure.execution.exit input result.1).layout), result.2))).map
        (fun result => (NativeEncodedResources.completeEncoding.encode
          (P.procedure.code, Configuration.reconstruct result.1.2 (cells result.1.1)), result.2)) := by
  exact P.representation_observation view cells equivalent
    (fun result => PMF.pure (NativeEncodedResources.completeEncoding.encode (P.procedure.code, result.1), result.2)) input

end Machine.NativeComponent
