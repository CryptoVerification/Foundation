import Foundation.Crypto.Semantics.Machine.Procedure
import Foundation.Constructions.Symmetric.EncryptThenMAC.TableMAC
import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityEncryption

/-! Actual native primitives inhabit the reusable procedure interface.
Retained tape prefixes and head positions are part of each contract; packet
preparation and surrounding control transfer require separate real execution. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrimitiveContracts
open Foundation.Probability Machine
set_option backward.isDefEq.respectTransparency false

structure Prefixes where
  input : List Bool
  output : List Bool

/-- A sampler for arbitrary-width bitstrings with retained physical prefixes. -/
noncomputable def bitstringKeygen (width : Nat) : Machine.Procedure Prefixes (Bits width) :=
  Machine.Procedure.ofFixed Machine.OneTimePad.keygen
    (fun retained => Machine.OneTimePad.state retained.input retained.output (List.replicate width true))
    (fun retained key => Machine.OneTimePad.finish 5 (retained.input ++ List.replicate width true)
      (retained.output ++ key.toList))
    (fun _ => uniform (Bits width)) (fun _ => 5 * width + 2)
    (fun retained => Machine.OneTimePad.keygen_typed_run width retained.input retained.output)

/-- The existing two-row native sampler is another inhabitant of the same
contract. Its finite code and exact physical endpoint are unchanged. -/
noncomputable def tableKeygen (width : Nat → Nat) (n : Nat) :
    Machine.Procedure Prefixes (TableMAC.Key (width n)) :=
  Machine.Procedure.ofFixed OneTimePad.Native.keygenCode
    (fun retained => Machine.OneTimePad.state retained.input retained.output (List.replicate (2 * width n) true))
    (fun retained key => Machine.OneTimePad.finish 5 (retained.input ++ List.replicate (2 * width n) true)
      (retained.output ++ Machine.OneTimePad.pairInput key.1.toList key.2.toList))
    (fun _ => (TableMAC.scheme width).keygen n) (fun _ => 5 * (2 * width n) + 2)
    (fun retained => by
      have h := Machine.OneTimePad.keygen_typed_run (2 * width n) retained.input retained.output
      simpa only [OneTimePad.Native.keygenCode, TableMAC.scheme, PMF.map_comp,
        Function.comp_def, TableMAC.splitKey_encoding] using h)

structure SignInput (width : Nat) where
  key : TableMAC.Key width
  ciphertext : Bool
  retained : Prefixes

structure PadInput (width : Nat) where
  key : Bits width
  message : Bits width
  retained : Prefixes

/-- The actual arbitrary-width XOR code is a third kind of native primitive.
Its input preparation is an explicit precondition, not a free computation. -/
noncomputable def padEncrypt (width : Nat) : Machine.Procedure (PadInput width) (Bits width) :=
  Machine.Procedure.ofFixed OneTimePad.Native.encryptionCode
    (fun input => Machine.OneTimePad.state input.retained.input input.retained.output
      (Machine.OneTimePad.pairInput input.key.toList input.message.toList))
    (fun input ciphertext => Machine.OneTimePad.finish 16
      (input.retained.input ++ Machine.OneTimePad.pairInput input.key.toList input.message.toList)
      (input.retained.output ++ ciphertext.toList))
    (fun input => PMF.pure (OneTimePad.encrypt input.key input.message)) (fun _ => 8 * width + 2)
    (fun input => by
      simpa only [OneTimePad.Native.encryptionCode, Bits.length_toList, OneTimePad.encrypt,
        Machine.OneTimePad.toList_xor, PMF.pure_map] using
        Machine.OneTimePad.xor_run input.retained.input input.retained.output
          input.key.toList input.message.toList (by simp))

noncomputable def tableSign (width : Nat) : Machine.Procedure (SignInput width) (Bits width) :=
  Machine.Procedure.ofFixed TableMAC.Native.signCode
    (fun input => Machine.OneTimePad.state input.retained.input input.retained.output
      (input.ciphertext :: Machine.OneTimePad.pairInput input.key.1.toList input.key.2.toList))
    (fun input tag => TableMAC.Native.finish
      (input.retained.input ++ input.ciphertext :: Machine.OneTimePad.pairInput input.key.1.toList input.key.2.toList)
      (input.retained.output ++ tag.toList))
    (fun input => PMF.pure (TableMAC.sign input.key input.ciphertext)) (fun _ => 8 * width + 4)
    (fun input => by
      simpa only [PMF.pure_map] using
        TableMAC.Native.sign_from_run input.key input.ciphertext input.retained.input input.retained.output)

noncomputable def oneBitKeygen : Machine.Procedure (List Bool) Bool :=
  Machine.Procedure.ofFixed OneBitEncryption.Native.keygenCode Configuration.initial
    IntegrityEncryption.keyFinish (fun _ => sampleBit) (fun _ => 2)
    IntegrityEncryption.keygen_configuration

@[simp] theorem tableKeygen_code (width : Nat → Nat) (n : Nat) :
    (tableKeygen width n).code = OneTimePad.Native.keygenCode := rfl

@[simp] theorem tableSign_code (width : Nat) : (tableSign width).code = TableMAC.Native.signCode := rfl

@[simp] theorem tableKeygen_budget (width : Nat → Nat) (n : Nat) (retained : Prefixes) :
    (tableKeygen width n).execution.budget retained = 5 * (2 * width n) + 2 := rfl

@[simp] theorem tableSign_budget (width : Nat) (input : SignInput width) :
    (tableSign width).execution.budget input = 8 * width + 4 := rfl

/-- These wrappers are built from existing native proofs, not new primitive
instructions or assumptions about the cost of a host-language function. -/
theorem tableSign_run (width : Nat) (input : SignInput width) (extra : Nat) :
    Machine.evalConfigWithin (tableSign width).code ((tableSign width).execution.entry input)
      (8 * width + 4 + extra) =
        ((tableSign width).execution.semantics input).map ((tableSign width).execution.exit input) := by
  apply (tableSign width).final_run input _ _ (by simp)
  intro output _
  rfl

end Foundation.Symmetric.EncryptThenMAC.PrimitiveContracts
