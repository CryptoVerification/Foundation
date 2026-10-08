import Foundation.Crypto.Semantics.Machine.NativePacketService
import Foundation.Crypto.Semantics.Machine.FreshMaskResponse

/-! Fresh-key encryption from an actual raw request buffer through physical
loading, native computation and packet delivery. No prepared tape is assumed.
The public request length determines the complete actual elapsed time. -/
namespace Machine.FreshMaskPacketService
open Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

theorem entry_equivalent (message : List Bool) :
    (NativePacketService.loaded message).Equivalent
      (FreshMaskResponse.component.procedure.execution.entry message) := by
  change (NativePacketService.loaded message).Equivalent
    (GeneratedBlockEncryption.link.native.execution.entry message).swapTapes
  rw [GeneratedBlockEncryption.entry]
  exact NativePacketService.loaded_equivalent message

noncomputable def execution (message : List Bool) :=
  NativePacketService.service FreshMaskResponse.component message message (entry_equivalent message)
    message.length (FreshMaskResponse.supported message)

theorem entry (message : List Bool) : (execution message).entry () = .loading message {} := rfl

theorem exit (message packet : List Bool) :
    (execution message).exit () packet = .executing (.returned packet) := rfl

theorem budget (message : List Bool) : (execution message).budget () = 67 * message.length + 47 := by
  rw [execution, NativePacketService.service_budget]
  change (3 * message.length + 3) +
    (GeneratedBlockEncryption.link.native.execution.budget message + (3 * message.length + 4)) = _
  rw [GeneratedBlockEncryption.budget]
  omega

theorem costed_uniform {width : Nat} (message : Bits width) :
    (execution message.toList).costed () =
      (uniform (Bits width)).map (fun ciphertext => (ciphertext.toList, 67 * width + 47)) := by
  rw [execution, NativePacketService.service_costed]
  rw [FreshMaskResponse.component, NativeComponent.swapTapes_firstArrival_costed]
  change ((GeneratedBlockEncryption.arrival.procedure.execution.costed message.toList).map _).map _ = _
  rw [GeneratedBlockEncryption.arrival_physical_uniform, PMF.map_comp, PMF.map_comp]
  congr 1
  funext ciphertext
  dsimp only [Function.comp_def]
  rw [FreshMaskResponse.output_bits, Bits.length_toList, Bits.length_toList]
  congr 1
  omega

theorem semantics_uniform {width : Nat} (message : Bits width) :
    (execution message.toList).semantics () = (uniform (Bits width)).map Bits.toList := by
  rw [← (execution message.toList).correct, costed_uniform, PMF.map_comp]
  rfl

/-- Full completion from the raw buffer, including loading and handoff. -/
theorem run {width : Nat} (message : Bits width) (horizon : Nat)
    (hTime : 67 * width + 47 ≤ horizon) :
    eval (NativePacketService.step FreshMaskResponse.component.procedure.code) horizon (.loading message.toList {}) =
      (uniform (Bits width)).map (fun ciphertext => .executing (.returned ciphertext.toList)) := by
  have h := (execution message.toList).final_run ()
    (fun packet _ => by simp [exit, NativePacketService.step, CellResponseExport.step, PMF.pure_map])
    horizon (by rw [budget, Bits.length_toList]; exact hTime)
  rw [entry, semantics_uniform, PMF.map_comp] at h
  exact h

theorem perfect_secrecy {width : Nat} (left right : Bits width)
    {Observed : Type*} (observer : List Bool × Nat → PMF Observed) :
    ((execution left.toList).costed ()).bind observer = ((execution right.toList).costed ()).bind observer := by
  rw [costed_uniform, costed_uniform]

end Machine.FreshMaskPacketService
