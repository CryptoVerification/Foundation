import Foundation.Crypto.Semantics.Oracle.RefreshInteraction

/-! Shared local independence and conditional kernel laws, without diagram
syntax or proof-certificate imports. -/
namespace CryptoOracle.ProofEdits.Interaction
open Foundation.Probability CryptoOracle.RandomOracle
set_option backward.isDefEq.respectTransparency false
variable {Input Tag : Type} [DecidableEq Input]

def independent : Action Input → Action Input → Bool
  | .query _, .record _ | .record _, .query _ => true
  | .record _, .refresh _ | .refresh _, .record _ => true
  | .refresh _, .refresh _ => true
  | .query request, .refresh coordinate | .refresh coordinate, .query request => decide (request ≠ coordinate)
  | _, _ => false

theorem scan_exchange (seen : Finset Input) (first second : Action Input) (tail : List (Action Input))
    (allowed : independent first second = true) :
    scan seen (first :: second :: tail) = scan seen (second :: first :: tail) := by
  cases first with
  | query request =>
      cases second with
      | query other => simp [independent] at allowed
      | record other => rfl
      | refresh coordinate =>
          simp only [independent, decide_eq_true_eq] at allowed
          simp [scan, Ne.symm allowed]
  | record message =>
      cases second with
      | query other => rfl
      | record other => simp [independent] at allowed
      | refresh other => rfl
  | refresh coordinate =>
      cases second with
      | query request =>
          simp only [independent, decide_eq_true_eq] at allowed
          simp [scan, Ne.symm allowed]
      | record other => rfl
      | refresh other =>
          by_cases left : coordinate ∈ seen <;> by_cases right : other ∈ seen <;> simp [scan, left, right]

variable [Fintype Tag] [Nonempty Tag]

theorem resample_exchange (state : State Input Tag) (first second : Input) :
    (resample state first).bind (fun next => resample next second) =
      (resample state second).bind (fun next => resample next first) := by
  have exchange := congrArg (PMF.map (fun pair : Unit × (Input → Tag) => { state with function := pair.2 }))
    (Refresh.step_exchange (fun input (_ : Unit) => input) first second ((), state.function))
  simpa [Refresh.step, resample, update, PMF.map_bind, PMF.bind_map, PMF.map_comp,
    Function.comp_def, PMF.map] using exchange

theorem step_exchange (first second : Action Input) (allowed : independent first second = true)
    (state : State Input Tag) :
    (step first state).bind (step second) = (step second state).bind (step first) := by
  cases first with
  | query request =>
      cases second with
      | query other => simp [independent] at allowed
      | record other => simp [step, ask_record]
      | refresh coordinate =>
          simp only [independent, decide_eq_true_eq] at allowed
          simp [step, resample, PMF.map, Function.comp_def, ask_update, allowed]
  | record message =>
      cases second with
      | query other => simp [step, ask_record]
      | record other => simp [independent] at allowed
      | refresh other => simp [step, resample, PMF.map, Function.comp_def, update_record]
  | refresh coordinate =>
      cases second with
      | query request =>
          simp only [independent, decide_eq_true_eq] at allowed
          simp [step, resample, PMF.map, Function.comp_def, ask_update, allowed]
      | record other => simp [step, resample, PMF.map, Function.comp_def, update_record]
      | refresh other => exact resample_exchange state coordinate other

end CryptoOracle.ProofEdits.Interaction
