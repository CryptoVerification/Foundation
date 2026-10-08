import Foundation.Examples.GeneratedBlockMask
import Foundation.Constructions.Symmetric.EncryptThenMAC.GeneratedBlockMaskNativeObserverPRG
import Foundation.Constructions.Symmetric.EncryptThenMAC.GeneratedBlockMaskNativeObserverResources

/-! Instantiate the generated-mask/native-observer pipeline with the fixed
uniform native generator. It recovers the established whole native-observer
pad execution at every horizon; this instance does not claim seed stretching. -/
namespace Foundation.Examples.GeneratedBlockMask.NativeObserver
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC
universe u v
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} {Output : Type v} (width : Nat → Nat) (n : Nat)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (message : Bits (width n)) (Q : Machine.Procedure Machine.Configuration Output)

theorem game_same (horizon : Nat) :
    GeneratedBlockMask.NativeObserver.game ((implementation width).native n)
      oracle state trace message () Q horizon =
      ReusableBlockPad.NativeObserver.game oracle state trace message Q horizon := rfl

variable (hEntry : ∀ machine, Q.execution.entry machine = machine.resumeAt 0)
    (hHalt : ∀ machine output, output ∈ (Q.execution.semantics machine).support →
      (Q.execution.exit machine output).halted = true)
    (cap : Nat) (hCap : ∀ ciphertext : List Bool, ciphertext.length = width n →
      Q.execution.budget (ReusableBlockPad.NativeObserver.publicCaller ciphertext) ≤ cap)

theorem uniform_budget :
    (GeneratedBlockMask.NativeObserver.whole ((implementation width).native n)
      ((implementation width).halt n) ((implementation width).tape n)
      ((implementation width).read n) ((implementation width).read_exit n)
      oracle state trace message () Q hEntry cap hCap).budget () = 55 * width n + 42 + cap := by
  rw [GeneratedBlockMask.NativeObserver.budget]
  change (5 * width n + 2) + 50 * width n + 40 + cap = _
  omega

include hEntry hHalt hCap in
/-- Replacing the old dedicated uniform experiment by the general generator
interface preserves its actual native-observer perfect-secrecy theorem. -/
theorem uniform_secrecy (other : Bits (width n)) (leftTime rightTime : Nat)
    (hLeft : 55 * width n + 42 + cap ≤ leftTime) (hRight : 55 * width n + 42 + cap ≤ rightTime) :
    GeneratedBlockMask.NativeObserver.game ((implementation width).native n)
      oracle state trace message () Q leftTime =
    GeneratedBlockMask.NativeObserver.game ((implementation width).native n)
      oracle state trace other () Q rightTime := by
  rw [game_same, game_same]
  exact ReusableBlockPad.NativeObserver.perfect_secrecy oracle state trace message Q
    hEntry hHalt cap hCap other leftTime rightTime hLeft hRight

end Foundation.Examples.GeneratedBlockMask.NativeObserver
