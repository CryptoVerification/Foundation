import Foundation.Crypto.Semantics.Oracle.FreshMaskCallerService
import Foundation.Crypto.Semantics.Oracle.PacketResponseServiceExactTime
import Foundation.Crypto.Semantics.Machine.FreshMaskPacketServiceExactTime

/-! Joint ciphertext, physical resumed caller and unpadded service cost.
The complete trace retains the request, so no secrecy of that full trace
is asserted by these execution equalities. -/
namespace CryptoOracle.Interactive.FreshMaskCallerService
open Foundation.Probability TimedExecution Foundation.Symmetric
universe u
set_option backward.isDefEq.respectTransparency false

theorem ready_boundary (component : Machine.NativePacketService.Control) :
    (ready component).isSome = Machine.NativePacketService.returned component := by
  cases component <;> simp [ready, Machine.NativePacketService.returned]
  rename_i component
  cases component <;> rfl

theorem handler_costed_uniform {width : Nat} (message : Bits width) :
    (handler message).execution.costed () =
      (uniform (Bits width)).map (fun ciphertext => (((), ciphertext.toList), 67 * width + 47)) := by
  change ((Machine.FreshMaskPacketService.execution message.toList).costed ()).map _ = _
  rw [Machine.FreshMaskPacketService.costed_uniform, PMF.map_comp]
  rfl

theorem handler_exact_first_ready {width : Nat} (message : Bits width) :
    (handler message).ExactFirstReady := by
  unfold PacketResponseService.Handler.ExactFirstReady
  have hb : (handler message).execution.budget () = 67 * width + 47 := by
    change (Machine.FreshMaskPacketService.execution message.toList).budget () = _
    rw [Machine.FreshMaskPacketService.budget, Bits.length_toList]
  have he : (handler message).execution.entry () = .loading message.toList {} := rfl
  rw [hb, he]
  have hBoundary : (fun component => (ready component).isSome) = Machine.NativePacketService.returned :=
    funext ready_boundary
  rw [hBoundary]
  change (runToBoundary (Machine.NativePacketService.step Machine.FreshMaskResponse.component.procedure.code)
    Machine.NativePacketService.returned (67 * width + 47) (.loading message.toList {})).map _ = _
  rw [Machine.FreshMaskPacketService.first_return_uniform, handler_costed_uniform, PMF.map_comp]
  rfl

variable {State : Type u} (code : Code) (oracle : BitOracle State)
    (caller : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    {width : Nat} (message : Bits width)

theorem costed_uniform : (execution code oracle caller state trace message).costed () =
    (uniform (Bits width)).map (fun ciphertext =>
      (((), NativeCallback.resumed caller state trace message.toList ciphertext.toList),
        70 * width + 51)) := by
  rw [execution, PacketResponseService.service_costed_of_exact componentStep begin ready absorbing
    code oracle caller state trace message.toList (handler message) (handler_exact_first_ready message),
    handler_costed_uniform, PMF.map_comp]
  congr 1
  funext ciphertext
  dsimp only [Function.comp_def]
  rw [Bits.length_toList]
  congr 1
  omega

theorem raw_costed_uniform (request : List Bool) :
    (rawExecution code oracle caller state trace request).costed () =
    (uniform (Bits request.length)).map (fun ciphertext =>
      (((), NativeCallback.resumed caller state trace request ciphertext.toList),
        70 * request.length + 51)) := by
  rw [rawExecution, costed_uniform, asBits_toList]

end CryptoOracle.Interactive.FreshMaskCallerService
