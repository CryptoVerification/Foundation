import Foundation.Crypto.Semantics.Oracle.OneUsePreparation
import Foundation.Examples.CheckedResponse

/-! Arbitrary-width XOR from separate physical operands to a resumed caller.
The key is still supplied in the private store; key generation is separate. -/
namespace Foundation.OneUsePreparationExamples
open Foundation.Probability TimedExecution CryptoOracle.Interactive
open Machine.OneTimePad.Prepared
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (code : Code) (oracle : BitOracle State) (saved : Machine.Configuration)
    (state : State) (trace : List (List Bool × List Bool)) (request : List Bool)

noncomputable def response (input : Machine.PairPreparation.Input) :=
  OneUseSource.preparedResponse code oracle saved state trace request listProcedure id
    CheckedResponseExamples.xor_halt CheckedResponseExamples.xor_tape
    (fun _ machine => machine.outputBits) (fun _ output => finish_output _ output [])
    (fun input => input.first.length)
    (fun input output h => by
      change output ∈ (PMF.pure (Machine.OneTimePad.xorList input.first input.second)).support at h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      exact le_of_eq (xorList_length input.first input.second input.sameLength))
    input input (by rfl)

theorem budget (input : Machine.PairPreparation.Input) :
    (response code oracle saved state trace request input).budget () = 31 * input.first.length + 29 := by
  unfold response
  rw [OneUseSource.preparedResponse_budget]
  change 12 * input.first.length + (8 * input.first.length + 2) + 11 * input.first.length + 27 = _
  omega

theorem distribution (input : Machine.PairPreparation.Input) :
    ((response code oracle saved state trace request input).costed ()).map
      (fun result => (response code oracle saved state trace request input).exit () result.1) =
      PMF.pure (OneUseSource.Control.source true
        (Machine.PairPreparation.operand [] input.first input.firstTail)
        (NativeCallback.resumed saved state trace request
          (true :: Machine.OneTimePad.xorList input.first input.second))) := by
  unfold response
  rw [OneUseSource.preparedResponse_distribution]
  simp [listProcedure, Machine.Procedure.ofFixed, Procedure.ofFixed, PMF.pure_map]
end Foundation.OneUsePreparationExamples
