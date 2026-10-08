import Foundation.Crypto.Semantics.Machine.ExportedProcedure
import Foundation.Constructions.Symmetric.EncryptThenMAC.ProjectedGeneratedBlockMaskPRG

/-! Native generator implementation from supported physical export facts.
Halting and output layout are required only on reachable outcomes. The
existing projected implementation and its security/resource theorems apply
without changing the code, input configuration or joint physical cost law. -/
namespace Foundation.Symmetric.EncryptThenMAC.ProjectedGeneratedBlockMask.PRG
open Machine Foundation.Probability Foundation.Symmetric TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false

structure PhysicalImplementation (G : Generator) where
  Input : Nat → Type u
  Output : Nat → Type v
  code : Machine.Program
  execution : ∀ n, TimedExecution.Procedure (stepPMF code) (Input n) (Output n)
  key : ∀ n, Machine.Configuration → Bits (G.outputLength n)
  exports : ∀ n input output, output ∈ ((execution n).semantics input).support →
    ExportedProcedure.Valid (key n) Bits.toList ((execution n).exit input output)
  implements : ∀ n input, ((execution n).semantics input).map
    (fun output => key n ((execution n).exit input output)) = G.real n

namespace PhysicalImplementation
variable {G : Generator} (I : PhysicalImplementation.{u,v} G)

def native (n : Nat) : Machine.Procedure (I.Input n) (I.Output n) := ⟨I.code, I.execution n⟩

/-- Certify only supported endpoint facts; the native execution is unchanged. -/
noncomputable def projected : Implementation G where
  Input := I.Input
  Result := fun n => ExportedProcedure.Result (I.key n) Bits.toList
  code := I.code
  execution := fun n => (ExportedProcedure.native (I.native n) (I.key n) Bits.toList (I.exports n)).execution
  key := fun n result => I.key n result.val
  halt := fun n => ExportedProcedure.halted (I.native n) (I.key n) Bits.toList (I.exports n)
  tape := fun n => ExportedProcedure.tape (I.native n) (I.key n) Bits.toList (I.exports n)
  read := fun n => ExportedProcedure.read (I.native n) (I.key n) Bits.toList (I.exports n)
  read_exit := fun n => ExportedProcedure.read_exit (I.native n) (I.key n) Bits.toList (I.exports n)
  implements := fun n input =>
    (ExportedProcedure.key_distribution (I.native n) (I.key n) Bits.toList (I.exports n) input).trans
      (I.implements n input)

theorem projected_code : I.projected.code = I.code := rfl

theorem projected_entry (n : Nat) (input : I.Input n) :
    (I.projected.execution n).entry input = (I.execution n).entry input := rfl

theorem projected_budget (n : Nat) (input : I.Input n) :
    (I.projected.execution n).budget input = (I.execution n).budget input := rfl

/-- Proof erasure recovers the complete physical result and cost together. -/
theorem projected_costed (n : Nat) (input : I.Input n) :
    ((I.projected.execution n).costed input).map (fun result => (result.1.val, result.2)) =
      ((I.execution n).costed input).map (fun result => ((I.execution n).exit input result.1, result.2)) :=
  ExportedProcedure.costed (I.native n) (I.key n) Bits.toList (I.exports n) input

end PhysicalImplementation
end Foundation.Symmetric.EncryptThenMAC.ProjectedGeneratedBlockMask.PRG
