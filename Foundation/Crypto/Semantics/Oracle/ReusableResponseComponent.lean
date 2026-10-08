import Foundation.Crypto.Semantics.Oracle.ReusableResponseSource
import Foundation.Crypto.Semantics.ProcedureBoundary

/-! Certified component execution in the repeated-request runtime. Actual
component stopping costs are kept; transfer to native export costs one step. -/
namespace CryptoOracle.Interactive.ReusableResponseComponent
open Foundation.Probability TimedExecution
universe u v w x
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v} {Saved : Type w} {Output : Type x}
    (componentStep : Component → PMF Component)
    (begin : Saved → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Saved))
    (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)
    (P : Procedure componentStep Unit Output)
    (machine : Output → Machine.Configuration) (retained : Output → Saved)
    (hReady : ∀ output, ready (P.exit () output) = some (machine output, retained output))
    (hAbsorb : ∀ component, (ready component).isSome = true → componentStep component = PMF.pure component)
    (read : Component → Output) (hRead : ∀ output, read (P.exit () output) = output)

noncomputable abbrev outerStep := ReusableResponseSource.step componentStep begin ready native code oracle

def boundary : ReusableResponseSource.Control Component State Saved → Bool
  | .processing _ _ _ _ component => (ready component).isSome
  | _ => true

noncomputable def body :=
  P.liftBoundary (fun component => (ready component).isSome)
    (fun input output _ => by cases input; simp [hReady]) hAbsorb
    (fun _ => read) (fun input output => by cases input; exact hRead output)
    (outerStep componentStep begin ready native code oracle) (boundary ready)
    (ReusableResponseSource.Control.processing caller state trace request) (fun _ => rfl)
    (by intro component h; cases hr : ready component with
        | none => simp [outerStep, ReusableResponseSource.step, hr]
        | some frame => simp [hr] at h)

noncomputable def transfer : Procedure (outerStep componentStep begin ready native code oracle) Output Unit :=
  Procedure.ofFixed _
    (fun output => .processing caller state trace request (P.exit () output))
    (fun output _ => .calling caller state trace request (.responding (.running (machine output))) (retained output))
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun output => by simp [TimedExecution.eval, outerStep, ReusableResponseSource.step, hReady, PMF.pure_map])

noncomputable def whole :=
  (body componentStep begin ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead).seq
    (transfer componentStep begin ready native code oracle caller state trace request P machine retained hReady)
    (fun _ _ _ => rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)

theorem budget :
    (whole componentStep begin ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead).budget () =
      P.budget () + 1 := rfl

theorem semantics :
    (whole componentStep begin ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead).semantics () =
      (P.semantics ()).map (fun output => (output, ())) := by
  change (P.semantics ()).bind (fun output => (PMF.pure ()).map (fun result => (output, result))) = _
  simp only [PMF.pure_map]
  rfl

theorem law (horizon : Nat) (hBudget : P.budget () + 1 ≤ horizon) :
    TimedExecution.eval (outerStep componentStep begin ready native code oracle) horizon
      (.processing caller state trace request (P.entry ())) =
      ((whole componentStep begin ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead).costed ()).bind
        (fun result => TimedExecution.eval (outerStep componentStep begin ready native code oracle) (horizon - result.2)
          (.calling caller state trace request (.responding (.running (machine result.1.1))) (retained result.1.1))) :=
  (whole componentStep begin ready native code oracle caller state trace request P machine retained hReady hAbsorb read hRead).law
    () horizon hBudget

end CryptoOracle.Interactive.ReusableResponseComponent
