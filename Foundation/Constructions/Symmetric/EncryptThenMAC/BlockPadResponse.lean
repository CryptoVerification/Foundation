import Foundation.Crypto.Semantics.Machine.FlaggedBlockXor
import Foundation.Constructions.Symmetric.EncryptThenMAC.ReusableResponseModel

/-! Arbitrary-width pad processing in the actual retained-key request layout.
This proves operational encryption and response delivery. Repeated calls
retain the same key, so no multi-use secrecy is inferred from this contract. -/
namespace Foundation.Symmetric.EncryptThenMAC.BlockPadResponse
open Machine Foundation.Probability TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric Foundation.Symmetric.OneTimePad
open Foundation.Symmetric.EncryptThenMAC.ResponseHandoffProgram
universe u
set_option backward.isDefEq.respectTransparency false

noncomputable def model (width : Nat) : Machine.ProcedureModel (Bits width × Bits width) Unit where
  procedure := Machine.Procedure.ofFixed FlaggedBlockXor.code
    (fun input => FlaggedBlockXor.initial input.1.toList input.2.toList)
    (fun input _ => FlaggedBlockXor.final input.1.toList input.2.toList)
    (fun _ => PMF.pure ()) (fun _ => 24 * width + 8)
    (fun input => by
      simpa [FlaggedBlockXor.final, PMF.pure_map] using
        FlaggedBlockXor.run input.1.toList input.2.toList (by simp))
  ideal := fun _ => PMF.pure ()
  implements := fun _ => rfl
  encode := fun input _ => (encrypt input.1 input.2).toList
  halt := fun _ _ _ => rfl
  output := by
    intro input output _
    change (FlaggedBlockXor.final input.1.toList input.2.toList).outputBits = _
    rw [FlaggedBlockXor.final_output]
    exact (Machine.OneTimePad.toList_xor input.1 input.2).symm

theorem model_entry {width : Nat} (key message : Bits width) :
    (model width).procedure.execution.entry (key, message) =
      preparedMachine key.toList (FlaggedBlockXor.request message.toList) := rfl

theorem model_tape {width : Nat} (key message : Bits width) (output : Unit)
    (_ : output ∈ ((model width).ideal (key, message)).support) :
    ((model width).procedure.execution.exit (key, message) output).outputTape =
      ResponseExport.endTape ((model width).encode (key, message) output) := by
  change (FlaggedBlockXor.final key.toList message.toList).outputTape =
    ResponseExport.endTape (encrypt key message).toList
  rw [FlaggedBlockXor.final_outputTape, ← Machine.OneTimePad.toList_xor key message]
  rfl

theorem model_cap {width : Nat} (key message : Bits width) (output : Unit)
    (_ : output ∈ ((model width).ideal (key, message)).support) :
    ((model width).encode (key, message) output).length ≤ width := by
  change (encrypt key message).toList.length ≤ width
  simp

variable {State : Type u} {width : Nat} (key message : Bits width)
    (code : Code) (oracle : BitOracle State) (caller : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool))

noncomputable def service :=
  ReusableResponse.Model.service (model width) (key, message) key.toList
    (FlaggedBlockXor.request message.toList) (model_entry key message) (model_tape key message)
    width (model_cap key message) code oracle caller state trace

theorem entry :
    (service key message code oracle caller state trace).entry () =
      .processing caller state trace (FlaggedBlockXor.request message.toList)
        (.headerWriting (retainedKey key.toList) (FlaggedBlockXor.request message.toList) {}) :=
  ReusableResponse.Model.entry _ _ _ _ _ _ _ _ _ _ _ _ _

theorem budget : (service key message code oracle caller state trace).budget () = 45 * width + 28 := by
  rw [service, ReusableResponse.Model.budget]
  change 9 * key.toList.length + 3 * (FlaggedBlockXor.request message.toList).length +
    (24 * width + 8) + 6 * width + 17 = _
  simp only [FlaggedBlockXor.request_length, Bits.length_toList]
  omega

theorem semantics :
    (service key message code oracle caller state trace).semantics () =
      PMF.pure (retainedKey key.toList,
        NativeCallback.resumed caller state trace (FlaggedBlockXor.request message.toList)
          (encrypt key message).toList) := by
  rw [service, ReusableResponse.Model.semantics]
  exact PMF.pure_map _ _

theorem time_polynomial {width : Nat → Nat} (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n => 45 * width n + 28) :=
  ((PolynomiallyBounded.const 45).mul hWidth).add (PolynomiallyBounded.const 28)

end Foundation.Symmetric.EncryptThenMAC.BlockPadResponse
