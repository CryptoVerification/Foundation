import Foundation.Crypto.Semantics.Oracle.OneUseDelivery
import Foundation.Crypto.Semantics.Oracle.FailureCallback

/-! Physical rejection delivery preserves the use flag and the private key.
Invalid lengths are rejected before any native procedure is started. -/
namespace CryptoOracle.Interactive.OneUseRejection
open Foundation.Probability TimedExecution
open OneUseSource
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (spent : Bool) (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
def failureBoundary : OneUseSource.Control State → Bool
  | .handling _ _ _ _ _ (.preparing component) => FailureCallback.boundary component
  | _ => true

def embedFailure (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (component : Machine.PreparationCheck.Control) : OneUseSource.Control State :=
  .handling false saved state trace request (.preparing component)

noncomputable def preparation (input : Machine.PreparationCheck.FailureInput) :=
  (Procedure.ofFixed Machine.PreparationCheck.step
    (fun _ : Unit => .preparing (.reading
      (Machine.PairPreparation.operand [] input.first input.firstTail)
      (Machine.PairPreparation.operand [] input.second input.secondTail) {}))
    (fun _ _ => Machine.PreparationCheck.final input) (fun _ => PMF.pure ())
    (fun _ => 12 * Machine.PreparationCheck.consumed input + 10)
    (fun _ => by simpa only [PMF.pure_map] using Machine.PreparationCheck.run input)).liftBoundary
    FailureCallback.boundary (fun _ _ _ => rfl)
    (fun component h => by
      cases component with
      | preparing component => cases component <;> simp_all [FailureCallback.boundary, Machine.PreparationCheck.step, Machine.PairPreparation.step, PMF.pure_map]
      | failure recovery => cases recovery <;> simp_all [FailureCallback.boundary, Machine.PreparationCheck.step, Machine.PreparationFailure.step, PMF.pure_map])
    (fun _ _ => ()) (fun _ _ => rfl)
    (OneUseSource.step native code oracle) failureBoundary (embedFailure saved state trace request) (fun _ => rfl)
    (fun component h => by
      cases component with
      | preparing component =>
        cases component <;> simp_all [FailureCallback.boundary, OneUseSource.step, CheckedCallback.step, embedFailure,
          PMF.map_comp, Function.comp_def] <;> rfl
      | failure recovery =>
        cases recovery <;> simp_all [FailureCallback.boundary, OneUseSource.step, CheckedCallback.step, embedFailure,
          PMF.map_comp, Function.comp_def] <;> rfl)

noncomputable def handoff (input : Machine.PreparationCheck.FailureInput) :
    Procedure (OneUseSource.step native code oracle) Unit Unit :=
  Procedure.ofFixed _
    (fun _ => embedFailure saved state trace request (Machine.PreparationCheck.final input))
    (fun _ _ => .handling false saved state trace request (.calling
      (Machine.PairPreparation.operand [] input.first input.firstTail)
      (Machine.PairPreparation.operand [] input.second input.secondTail)
      (.responding (.running (OneUseDelivery.packetMachine [false])))))
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by simp [TimedExecution.eval, OneUseSource.step, CheckedCallback.step, embedFailure,
      Machine.PreparationCheck.final, OneUseDelivery.packetMachine, PMF.pure_map])

noncomputable def whole (input : Machine.PreparationCheck.FailureInput) :=
  ((preparation native code oracle saved state trace request input).seq
    (handoff native code oracle saved state trace request input) (fun _ _ _ => rfl)
    (fun _ => 1) (fun _ _ _ => Nat.le_refl _)).seq
    ((OneUseDelivery.packetDelivery native code oracle false saved state trace request
      (Machine.PairPreparation.operand [] input.first input.firstTail)
      (Machine.PairPreparation.operand [] input.second input.secondTail)).reindex (fun _ => [false]))
    (fun _ _ _ => rfl) (fun _ => 14) (fun _ _ _ => Nat.le_refl _)

theorem budget (input : Machine.PreparationCheck.FailureInput) :
    (whole native code oracle saved state trace request input).budget () =
      12 * Machine.PreparationCheck.consumed input + 25 := by
  change (12 * Machine.PreparationCheck.consumed input + 10) + 1 + 14 = _
  omega

theorem whole_semantics (input : Machine.PreparationCheck.FailureInput) :
    (whole native code oracle saved state trace request input).semantics () =
      PMF.pure (((), ()), ([false], ())) := by
  simp [whole, preparation, handoff, OneUseDelivery.packetDelivery, OneUseDelivery.packetBody, OneUseDelivery.reply, NativeCallback.exported,
    OneUseDelivery.packetReady, Machine.Procedure.ofFixed,
    Procedure.seq, Procedure.reindex, Procedure.ofFixed, Procedure.liftBoundary,
    Procedure.frame, PMF.pure_map, Function.comp_def]

def resumed (input : Machine.PreparationCheck.FailureInput) : OneUseSource.Control State :=
  .source false (Machine.PairPreparation.operand [] input.first input.firstTail)
    (NativeCallback.resumed saved state trace request [false])

theorem distribution (input : Machine.PreparationCheck.FailureInput) :
    ((whole native code oracle saved state trace request input).costed ()).map
      (fun result => (whole native code oracle saved state trace request input).exit () result.1) =
      PMF.pure (resumed saved state trace request input) := by
  have h := congrArg (fun distribution => distribution.map
    ((whole native code oracle saved state trace request input).exit ()))
    ((whole native code oracle saved state trace request input).correct ())
  rw [whole_semantics, PMF.pure_map] at h
  have he : (whole native code oracle saved state trace request input).exit () (((), ()), ([false], ())) =
      resumed saved state trace request input := by rfl
  rw [he] at h
  simpa only [PMF.map_comp, Function.comp_def] using h
/-- Residual fuel executes the actual caller after the first return. -/
theorem resume_law (input : Machine.PreparationCheck.FailureInput) (horizon : Nat)
    (hBudget : 12 * Machine.PreparationCheck.consumed input + 25 ≤ horizon) :
    TimedExecution.eval (OneUseSource.step native code oracle) horizon
      (.handling false saved state trace request (.preparing (.preparing (.reading
        (Machine.PairPreparation.operand [] input.first input.firstTail)
        (Machine.PairPreparation.operand [] input.second input.secondTail) {})))) =
      ((whole native code oracle saved state trace request input).costed ()).bind
        (fun result => TimedExecution.eval (OneUseSource.step native code oracle)
          (horizon - result.2) (resumed saved state trace request input)) := by
  have h := (whole native code oracle saved state trace request input).law () horizon
    (by rw [budget]; exact hBudget)
  change TimedExecution.eval _ _ ((whole native code oracle saved state trace request input).entry ()) = _
  rw [h]
  rw [← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result hResult
  have hs := (whole native code oracle saved state trace request input).result_support () result hResult
  rw [whole_semantics, PMF.mem_support_pure_iff] at hs
  rw [hs]
  rfl

end CryptoOracle.Interactive.OneUseRejection
