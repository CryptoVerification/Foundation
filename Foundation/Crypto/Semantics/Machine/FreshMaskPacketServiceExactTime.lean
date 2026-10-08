import Foundation.Crypto.Semantics.Machine.FreshMaskPacketService
import Foundation.Crypto.Semantics.Machine.NativePacketServiceExactTime

/-! The fresh-key example's certified joint cost is its actual first-return
law, not merely the time at which a padded execution can be observed. -/
namespace Machine.FreshMaskPacketService
open Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

theorem costed_is_first_return (message : List Bool) :
    ((execution message).costed ()).map
      (fun result => (NativePacketService.Control.executing (.returned result.1), result.2)) =
    runToBoundary (NativePacketService.step FreshMaskResponse.component.procedure.code)
      NativePacketService.returned (67 * message.length + 47) (.loading message {}) := by
  have h := NativePacketService.costed_is_first_return FreshMaskResponse.component message message
    (entry_equivalent message) message.length (FreshMaskResponse.supported message)
  have hb := budget message
  change (3 * message.length + 3) +
    (FreshMaskResponse.component.procedure.execution.budget message + (3 * message.length + 4)) =
    67 * message.length + 47 at hb
  rw [hb] at h
  exact h

/-- Output and the actual first-return time are independent of the plaintext. -/
theorem first_return_uniform {width : Nat} (message : Bits width) :
    runToBoundary (NativePacketService.step FreshMaskResponse.component.procedure.code)
      NativePacketService.returned (67 * width + 47) (.loading message.toList {}) =
    (uniform (Bits width)).map
      (fun ciphertext => (NativePacketService.Control.executing (.returned ciphertext.toList),
        67 * width + 47)) := by
  have h := costed_is_first_return message.toList
  rw [Bits.length_toList] at h
  rw [← h, costed_uniform, PMF.map_comp]
  rfl

theorem first_return_perfect_secrecy {width : Nat} (left right : Bits width)
    {Observed : Type*} (observer : NativePacketService.Control × Nat → PMF Observed) :
    (runToBoundary (NativePacketService.step FreshMaskResponse.component.procedure.code)
      NativePacketService.returned (67 * width + 47) (.loading left.toList {})).bind observer =
    (runToBoundary (NativePacketService.step FreshMaskResponse.component.procedure.code)
      NativePacketService.returned (67 * width + 47) (.loading right.toList {})).bind observer := by
  rw [first_return_uniform, first_return_uniform]

end Machine.FreshMaskPacketService
