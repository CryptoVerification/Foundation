import Foundation.Constructions.Symmetric.EncryptThenMAC.ResponseHandoffCallback

/-! A concrete finite acknowledgement handler exercises the entire callback
for arbitrary key and payload lengths. This is an execution example, not a
claim of cryptographic security for an acknowledgement protocol. -/
namespace Foundation.Examples.RetainedResponseCallback
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC
open ResponseHandoffProgram
universe u
set_option backward.isDefEq.respectTransparency false

def native : Program := [.write .output false, .moveRight .output, .halt]

def finish (key payload : List Bool) : Machine.Configuration :=
  { preparedMachine key payload with pc := 2, outputTape := ResponseExport.endTape [false], halted := true }

noncomputable def handler (key payload : List Bool) :=
  Machine.Procedure.ofFixed native (fun _ : Unit => preparedMachine key payload)
    (fun _ _ : Unit => finish key payload) (fun _ => PMF.pure ()) (fun _ => 3)
    (fun _ => by
      simp [evalConfigWithin, stepPMF, next, native, finish, preparedMachine,
        Instruction.next, Configuration.updateTape, Configuration.advance,
        Tape.write, Tape.moveRight, ResponseExport.endTape, PMF.pure_map])

variable {State : Type u} (code : Code) (oracle : BitOracle State)
    (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request key payload : List Bool)

noncomputable def whole :=
  Callback.whole native code oracle caller state trace request key payload
    (handler key payload).execution rfl (fun _ => ()) (fun _ => rfl)
    (fun _ => [false]) (fun _ => rfl) (fun _ => rfl) 1
    (fun _ _ => Nat.le_refl _)

theorem budget : (whole code oracle caller state trace request key payload).budget () =
    9 * key.length + 3 * payload.length + 25 := by
  rw [whole, Callback.budget]
  change 9 * key.length + 3 * payload.length + 3 + 6 * 1 + 16 = _
  omega

theorem distribution :
    ((whole code oracle caller state trace request key payload).costed ()).map
      (fun result => (whole code oracle caller state trace request key payload).exit () result.1) =
      PMF.pure (ComponentResponseCallback.Control.delivering
        (.source (NativeCallback.resumed caller state trace request [false]), retainedKey key)) := by
  rw [whole, Callback.distribution]
  change (PMF.pure ()).map _ = _
  rw [PMF.pure_map]

end Foundation.Examples.RetainedResponseCallback
