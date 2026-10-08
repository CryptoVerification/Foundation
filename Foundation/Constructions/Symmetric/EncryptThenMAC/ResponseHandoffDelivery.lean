import Foundation.Constructions.Symmetric.EncryptThenMAC.ResponseHandoffRepeated
import Foundation.Crypto.Semantics.Oracle.RetainedResponseDelivery

/-! Delivery contract for the exact halted native handler exit, with the
retained private key carried separately. Preparing the export controller's
entry and connecting the caller's next request are separate obligations. -/
namespace Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram.HandlerDelivery
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
universe u v
set_option backward.isDefEq.respectTransparency false

variable {Output : Type u} (program : Program)
    (handler : TimedExecution.Procedure (stepPMF program) Unit Output)
    (encode : Output → List Bool)
    (hHalt : ∀ output, (handler.exit () output).halted = true)
    (hTape : ∀ output, (handler.exit () output).outputTape = ResponseExport.endTape (encode output))

/-- This packages proofs about the existing physical exit; it does not
construct the packet on a new tape. -/
def input (output : Output) : RetainedResponseDelivery.Input :=
  ⟨handler.exit () output, encode output, hHalt output, hTape output⟩

variable {State : Type v} (code : Code) (oracle : BitOracle State)
    (saved : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request key : List Bool)

noncomputable def delivery (output : Output) :=
  (RetainedResponseDelivery.framed program code oracle saved state trace request
    (input program handler encode hHalt hTape output) Tape).reindex
    (fun _ : Unit => ((), retainedKey key))

theorem entry (output : Output) :
    (delivery program handler encode hHalt hTape code oracle saved state trace request key output).entry () =
      (NativeCallback.Control.responding (.running (handler.exit () output)), retainedKey key) := rfl

theorem budget (output : Output) :
    (delivery program handler encode hHalt hTape code oracle saved state trace request key output).budget () =
      6 * (encode output).length + 7 :=
  RetainedResponseDelivery.framed_budget program code oracle saved state trace request
    (input program handler encode hHalt hTape output) (retainedKey key)

theorem distribution (output : Output) :
    ((delivery program handler encode hHalt hTape code oracle saved state trace request key output).costed ()).map
      (fun result => (delivery program handler encode hHalt hTape code oracle saved state trace request key output).exit () result.1) =
      PMF.pure (NativeCallback.Control.source
        (NativeCallback.resumed saved state trace request (encode output)), retainedKey key) :=
  RetainedResponseDelivery.framed_distribution program code oracle saved state trace request
    (input program handler encode hHalt hTape output) (retainedKey key)

theorem retained_prefix (output : Output) (horizon : Nat)
    (target : NativeCallback.Control State × Tape)
    (hTarget : target ∈ (TimedExecution.eval
      (framedStep (NativeCallback.step program code oracle saved state trace request)) horizon
      (NativeCallback.Control.responding (.running (handler.exit () output)), retainedKey key)).support) :
    target.2 = retainedKey key :=
  framed_saved _ horizon _ (retainedKey key) target hTarget

end Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram.HandlerDelivery
