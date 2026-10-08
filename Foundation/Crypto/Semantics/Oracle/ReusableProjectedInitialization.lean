import Foundation.Crypto.Semantics.Oracle.ReusableResponseInitialization
import Foundation.Crypto.Semantics.Machine.ProjectedPrivateInitialization

/-! Reusable private initialization with distinct native internal results and
exported keys. Only the key must decode from the physically restored key tape;
retained seed/scratch information need not be reconstructible from that key. -/
namespace CryptoOracle.Interactive.ReusableResponseInitialization.Projected
open Machine Foundation.Probability TimedExecution
universe u v w x y
set_option backward.isDefEq.respectTransparency false
variable {Component : Type u} {State : Type v} {Input : Type w} {Result : Type x} {Key : Type y}
    (componentStep : Component → PMF Component) (begin : Tape → List Bool → Component)
    (ready : Component → Option (Machine.Configuration × Tape))
    (native : Machine.Program) (code : Code) (oracle : BitOracle State) (caller : Configuration State)
    (P : Machine.Procedure Input Result) (key : Result → Key) (encode : Key → List Bool)
    (hHalt : ∀ input result, (P.execution.exit input result).halted = true)
    (hTape : ∀ input result, (P.execution.exit input result).outputTape = ResponseExport.endTape (encode (key result)))
    (read : Input → Machine.Configuration → Result)
    (hRead : ∀ input result, read input (P.execution.exit input result) = result)
    (cap : Input → Nat)
    (hCap : ∀ input result, result ∈ (P.execution.semantics input).support → (encode (key result)).length ≤ cap input)
    (decode : Tape → Key)
    (hDecode : ∀ output, decode (ResponseExport.fromCells ((encode output).map some ++ [none])) = output)

noncomputable def sampling :=
  (PrivateInitialization.Projected.sample P key encode hHalt hTape read hRead cap hCap).liftBoundary
    readyBoundary (fun _ _ _ => rfl)
    (fun component h => by cases component <;> simp_all [readyBoundary, PrivateInitialization.step])
    (fun _ component => match component with | .ready tape => decode tape | _ => decode {})
    (fun _ _ => by
      simp only [PrivateInitialization.Projected.sample, TimedExecution.Procedure.observe, hDecode])
    (step componentStep begin ready P.code native code oracle caller) boundary Control.initializing (fun _ => rfl)
    (fun component h => by cases component <;> simp_all [readyBoundary, step])

noncomputable def transfer : TimedExecution.Procedure
    (step componentStep begin ready P.code native code oracle caller) Key Unit :=
  TimedExecution.Procedure.ofFixed _
    (fun output => .initializing (.ready (ResponseExport.fromCells ((encode output).map some ++ [none]))))
    (fun output _ => .active (.source
      (ResponseExport.fromCells ((encode output).map some ++ [none])).moveLeft.moveRight caller))
    (fun _ => PMF.pure ()) (fun _ => 2)
    (fun _ => by simp [TimedExecution.eval, step, PMF.pure_map])

noncomputable def initialization :=
  (sampling componentStep begin ready native code oracle caller P key encode hHalt hTape read hRead cap hCap decode hDecode).seq
    (transfer componentStep begin ready native code oracle caller P encode) (fun _ _ _ => rfl)
    (fun _ => 2) (fun _ _ _ => Nat.le_refl _)

theorem budget (input : Input) :
    (initialization componentStep begin ready native code oracle caller P key encode hHalt hTape read hRead cap hCap decode hDecode).budget input =
      P.execution.budget input + cap input + 4 := by
  change (P.execution.budget input + cap input + 2) + 2 = _
  omega

theorem semantics (input : Input) :
    (initialization componentStep begin ready native code oracle caller P key encode hHalt hTape read hRead cap hCap decode hDecode).semantics input =
      (P.execution.semantics input).map (fun result => (key result, ())) := by
  simp only [initialization, sampling, TimedExecution.Procedure.seq, TimedExecution.Procedure.liftBoundary,
    PrivateInitialization.Projected.sample, TimedExecution.Procedure.observe, PrivateInitialization.sample,
    TimedExecution.Procedure.ofFixed, transfer, PMF.bind_map, Function.comp_def, PMF.pure_map]
  rfl

/-- Every original physical generation stage is still executed. The final
private store is determined only by the projected key, after real transfer. -/
theorem distribution (input : Input) :
    ((initialization componentStep begin ready native code oracle caller P key encode hHalt hTape read hRead cap hCap decode hDecode).costed input).map
      (fun result => (initialization componentStep begin ready native code oracle caller P key encode
        hHalt hTape read hRead cap hCap decode hDecode).exit input result.1) =
      (P.execution.semantics input).map (fun result => Control.active (ReusableResponseSource.Control.source
        (ResponseExport.fromCells ((encode (key result)).map some ++ [none])).moveLeft.moveRight caller)) := by
  have h := congrArg (fun law => law.map
    ((initialization componentStep begin ready native code oracle caller P key encode hHalt hTape read hRead cap hCap decode hDecode).exit input))
    ((initialization componentStep begin ready native code oracle caller P key encode hHalt hTape read hRead cap hCap decode hDecode).correct input)
  rw [semantics] at h
  simp only [PMF.map_comp, Function.comp_def] at h
  exact h

end CryptoOracle.Interactive.ReusableResponseInitialization.Projected
