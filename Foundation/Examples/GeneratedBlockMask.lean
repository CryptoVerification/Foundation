import Foundation.Constructions.Symmetric.EncryptThenMAC.GeneratedBlockMaskResources
import Foundation.Constructions.Symmetric.OneTimePadNative

/-! Fully instantiate the uniform implementation interface using actual
native random-bit generation. This recovers the previously checked pad
experiment at every horizon, without an extra operational transition. -/
namespace Foundation.Examples.GeneratedBlockMask
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC
universe u
set_option backward.isDefEq.respectTransparency false

noncomputable def implementation (width : Nat → Nat) :
    GeneratedBlockMask.PRG.Implementation (OneTimePad.Native.generator width) where
  Input := fun _ => Unit
  code := Machine.OneTimePad.keygen
  execution := fun n => (Machine.PrivateBitGeneration.native (width n)).execution
  halt := fun n => Machine.PrivateBitGeneration.halted (width n)
  tape := fun n => Machine.PrivateBitGeneration.tape (width n)
  read := fun n => Machine.PrivateBitGeneration.read (width n)
  read_exit := fun n => Machine.PrivateBitGeneration.read_exit (width n)
  implements := by
    intro n input
    change uniform (Bits (width n)) = (uniform (Bits (width n))).map id
    rw [PMF.map_id]

variable {State : Type u} (width : Nat → Nat) (n : Nat) (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (message : Bits (width n))

theorem ciphertext_same (horizon : Nat) :
    GeneratedBlockMask.ciphertext ((implementation width).native n) oracle state trace message () horizon =
      ReusableBlockPad.ciphertext oracle state trace message horizon := rfl

theorem uniform_budget :
    (GeneratedBlockMask.whole ((implementation width).native n)
      ((implementation width).halt n) ((implementation width).tape n)
      ((implementation width).read n) ((implementation width).read_exit n)
      oracle state trace message).budget () = 55 * width n + 41 := by
  rw [Foundation.Symmetric.EncryptThenMAC.GeneratedBlockMask.budget]
  change (5 * width n + 2) + 50 * width n + 39 = _
  omega

end Foundation.Examples.GeneratedBlockMask
