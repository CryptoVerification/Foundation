import Foundation.Crypto.Semantics.Machine.CryptoInterfaces
import Foundation.Examples.BitMachineExecution

namespace Machine.Examples

open Foundation.Probability

/-- A toy goal whose adversary makes one probabilistic Boolean response to
the sole protocol request. Its advantage is always zero. -/
def bitGoal : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun _ _ => Unit → ProbComp Bool
  advantage := fun _ _ _ => 0

/-- Here `assemble` is just the identity on the observable response oracle.
The machine semantics still supplies that oracle through `responseWithin`. -/
def bitInterface : MachineAdversaryInterface bitGoal where
  Request := fun _ _ => Unit
  Response := fun _ _ => Bool
  instanceEncoding := fun _ => FiniteBitEncoding.unit
  requestEncoding := fun _ _ => FiniteBitEncoding.unit
  responseEncoding := fun _ _ => FiniteBitEncoding.bool
  fallback := fun _ _ => false
  assemble := fun _ _ respond => respond

def bitFamily : InstanceFamily bitGoal := fun _ => ()

/-- The finite instruction list is selected once, before the quantification
over all security parameters. It is never a family-indexed program type. -/
example : bitInterface.Realizes bitFamily randomOutputBit (fun _ => 2)
    (bitInterface.realizeFamily bitFamily randomOutputBit (fun _ => 2)) := rfl

example (n : Nat) : (encodeSecurityParameter n).length = n + 1 := by
  simp [encodeSecurityParameter]

example (n : Nat) :
    bitInterface.machineInput n () () =
      encodeSecurityParameter n ++ frame [] ++ frame [] := rfl

/-- The complete toy input has length `n + 3`, including delimiters. -/
def bitInputSize : bitInterface.InputSizeBound bitFamily where
  limit n := n + 3
  length_le := by
    intro n request
    cases request
    simp [MachineAdversaryInterface.machineInput, bitInterface,
      bitFamily, FiniteBitEncoding.unit, encodeSecurityParameter, frame]

example : (FiniteBitEncoding.bool).decode
    ((FiniteBitEncoding.bool).encode true) = some true := rfl

/-- The DDH adapter can be constructed once codes for current parameters
and the three challenge elements are supplied. -/
example (S : DDHSemantics ProbComp)
    (parameters : FiniteBitEncoding DDHParameters)
    (triples : ∀ params : DDHParameters,
      FiniteBitEncoding (params.Element × params.Element × params.Element)) :
    MachineAdversaryInterface (DDH ProbComp S) :=
  ddhInterface S parameters triples

/-- The two-stage IND-CPA adapter is likewise conditional on concrete finite
scheme/request/response encodings and a default message. -/
noncomputable example (S : INDCPASemantics ProbComp)
    (schemes : FiniteBitEncoding (PKE ProbComp))
    (requests : ∀ scheme : PKE ProbComp,
      FiniteBitEncoding (scheme.PublicKey ⊕ (List Bool × scheme.Ciphertext)))
    (responses : ∀ scheme : PKE ProbComp,
      FiniteBitEncoding
        ((scheme.Message × scheme.Message × List Bool) ⊕ Bool))
    (defaultMessage : ∀ scheme : PKE ProbComp, scheme.Message) :
    MachineAdversaryInterface (INDCPA ProbComp S) :=
  indCPAInterface S schemes requests responses defaultMessage

end Machine.Examples
