import Foundation.Crypto.Semantics.Oracle.PacketResponseService
import Foundation.Crypto.Semantics.Machine.FreshMaskPacketService

/-! Concrete native fresh-key masking service returning to a real caller.
Input loading, random computation, physical export, caller loading and
release are all present. The caller's next instruction is not executed. -/
namespace CryptoOracle.Interactive.FreshMaskCallerService
open Foundation.Probability TimedExecution Foundation.Symmetric
universe u
set_option backward.isDefEq.respectTransparency false

noncomputable def componentStep := Machine.NativePacketService.step Machine.FreshMaskResponse.component.procedure.code

def begin (_ : Unit) (request : List Bool) : Machine.NativePacketService.Control := .loading request {}

def ready : Machine.NativePacketService.Control → Option (Unit × List Bool)
  | .executing (.returned packet) => some ((), packet)
  | _ => none

theorem absorbing (component : Machine.NativePacketService.Control) (h : (ready component).isSome = true) :
    componentStep component = PMF.pure component := by
  cases component <;> simp_all [ready]
  rename_i component
  cases component <;> simp_all [ready, componentStep, Machine.NativePacketService.step, Machine.CellResponseExport.step, PMF.pure_map]

noncomputable def handler {width : Nat} (message : Bits width) :
    PacketResponseService.Handler componentStep ready where
  execution := (Machine.FreshMaskPacketService.execution message.toList).observe (fun packet => ((), packet))
    (fun _ output => .executing (.returned output.2)) (fun _ _ _ => rfl)
  ready_exit := fun output => by rcases output with ⟨retained, packet⟩; cases retained; rfl
  read := fun component => (ready component).getD ((), [])
  read_exit := fun output => by rcases output with ⟨retained, packet⟩; cases retained; rfl
  responseCap := width
  response_bound := by
    intro output hOutput
    change output ∈ (((Machine.FreshMaskPacketService.execution message.toList).semantics ()).map
      (fun packet => ((), packet))).support at hOutput
    rw [Machine.FreshMaskPacketService.semantics_uniform, PMF.map_comp, PMF.mem_support_map_iff] at hOutput
    obtain ⟨ciphertext, _, rfl⟩ := hOutput
    exact (Bits.length_toList ciphertext).le

variable {State : Type u} (code : Code) (oracle : BitOracle State)
    (caller : Machine.Configuration) (state : State) (trace : List (List Bool × List Bool))
    {width : Nat} (message : Bits width)

noncomputable def execution :=
  PacketResponseService.service componentStep begin ready absorbing code oracle caller state trace message.toList (handler message)

theorem entry : (execution code oracle caller state trace message).entry () =
    .processing caller state trace message.toList (begin () message.toList) := rfl

theorem budget : (execution code oracle caller state trace message).budget () = 70 * width + 51 := by
  rw [execution, PacketResponseService.service_budget]
  change (Machine.FreshMaskPacketService.execution message.toList).budget () + (3 * width + 4) = _
  rw [Machine.FreshMaskPacketService.budget, Bits.length_toList]
  omega

/-- Complete physical caller state, preserved external state and trace,
with a uniform ciphertext written into the caller's output tape. -/
theorem semantics : (execution code oracle caller state trace message).semantics () =
    (uniform (Bits width)).map (fun ciphertext =>
      ((), NativeCallback.resumed caller state trace message.toList ciphertext.toList)) := by
  rw [execution, PacketResponseService.service_semantics]
  change (((Machine.FreshMaskPacketService.execution message.toList).semantics ()).map
    (fun packet => ((), packet))).map _ = _
  rw [Machine.FreshMaskPacketService.semantics_uniform, PMF.map_comp, PMF.map_comp]
  rfl

/-- Length indexing is proof-side only; the runtime receives the original
raw list and executes the same code for every request length. -/
def asBits (request : List Bool) : Bits request.length := fun index => request[index.val]

theorem asBits_toList (request : List Bool) : (asBits request).toList = request := List.ofFn_getElem

noncomputable def rawExecution (request : List Bool) :=
  execution code oracle caller state trace (asBits request)

theorem raw_entry (request : List Bool) : (rawExecution code oracle caller state trace request).entry () =
    .processing caller state trace request (begin () request) := by
  rw [rawExecution, entry, asBits_toList]

theorem raw_budget (request : List Bool) : (rawExecution code oracle caller state trace request).budget () =
    70 * request.length + 51 := budget code oracle caller state trace (asBits request)

theorem raw_semantics (request : List Bool) : (rawExecution code oracle caller state trace request).semantics () =
    (uniform (Bits request.length)).map (fun ciphertext =>
      ((), NativeCallback.resumed caller state trace request ciphertext.toList)) := by
  rw [rawExecution, semantics, asBits_toList]

end CryptoOracle.Interactive.FreshMaskCallerService
