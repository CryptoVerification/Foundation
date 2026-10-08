import Foundation.Crypto.Semantics.Machine.PrivateInitialization
import Foundation.Crypto.Semantics.ProcedureIteration

/-! A native generator may retain a seed or scratch data in its result.
Project to the exported key only after the existing operational transfer has
discarded that native machine and physically rewound its output tape. The
projection need not be injective and is never executed as a machine primitive. -/
namespace Machine.PrivateInitialization.Projected
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {Input : Type u} {Result : Type v} {Key : Type w}
    (P : Machine.Procedure Input Result) (key : Result → Key) (encode : Key → List Bool)
    (hHalt : ∀ input result, (P.execution.exit input result).halted = true)
    (hTape : ∀ input result, (P.execution.exit input result).outputTape = ResponseExport.endTape (encode (key result)))
    (read : Input → Configuration → Result)
    (hRead : ∀ input result, read input (P.execution.exit input result) = result)
    (cap : Input → Nat)
    (hCap : ∀ input result, result ∈ (P.execution.semantics input).support → (encode (key result)).length ≤ cap input)

noncomputable def sample : TimedExecution.Procedure (PrivateInitialization.step P.code) Input Key :=
  (PrivateInitialization.sample P (fun result => encode (key result)) hHalt hTape read hRead cap hCap).observe key
    (fun _ output => .ready (ResponseExport.fromCells ((encode output).map some ++ [none])))
    (fun _ _ _ => rfl)

theorem budget (input : Input) :
    (sample P key encode hHalt hTape read hRead cap hCap).budget input =
      P.execution.budget input + cap input + 2 := rfl

theorem semantics (input : Input) :
    (sample P key encode hHalt hTape read hRead cap hCap).semantics input =
      (P.execution.semantics input).map key := rfl

/-- The final physical store depends on the exported key only after the
actual native generation, ownership transfer and cellwise rewind. -/
theorem physical_distribution (input : Input) :
    ((PrivateInitialization.procedure P (fun result => encode (key result)) hHalt hTape read hRead cap hCap).costed input).map
      (fun result => (PrivateInitialization.procedure P (fun result => encode (key result))
        hHalt hTape read hRead cap hCap).exit input result.1) =
      (P.execution.semantics input).map (fun result =>
        Control.ready (ResponseExport.fromCells ((encode (key result)).map some ++ [none]))) :=
  PrivateInitialization.distribution P (fun result => encode (key result)) hHalt hTape read hRead cap hCap input

end Machine.PrivateInitialization.Projected
