import Foundation.Crypto.Semantics.Machine.ResponseExport
import Foundation.Crypto.Semantics.Oracle.ResponseLoading

/-! A fixed native component returns its physically exported packet to a
suspended source. Native execution, extraction, ownership transfer, loading
and resumption are charged. Preparation of the native entry is separate. -/
namespace CryptoOracle.Interactive.NativeCallback
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false

inductive Control (State : Type u) where
  | responding (component : Machine.ResponseExport.Control)
  | source (frame : Configuration State)

variable {State : Type u}

def loading (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request packet : List Bool) : Configuration State :=
  ⟨state, .loading machine packet {}, (request, packet) :: trace⟩

def resumed (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request packet : List Bool) : Configuration State :=
  ⟨state, .running { machine with outputTape := ResponseLoading.loaded packet }, (request, packet) :: trace⟩

noncomputable def step (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) : Control State → PMF (Control State)
  | .responding (.returned packet) => PMF.pure (.source (loading machine state trace request packet))
  | .responding component => (Machine.ResponseExport.step native component).map .responding
  | .source frame => (Reification.timedStep code oracle frame).map .source

def exportBoundary : Machine.ResponseExport.Control → Bool
  | .returned _ => true
  | _ => false

def callbackBoundary : Control State → Bool
  | .responding component => exportBoundary component
  | .source _ => true

def packetRead : Machine.ResponseExport.Control → List Bool
  | .returned packet => packet
  | _ => []

theorem source_eval (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) (fuel : Nat)
    (frame : Configuration State) :
    TimedExecution.eval (step native code oracle machine state trace request) fuel (.source frame) =
      (TimedExecution.eval (Reification.timedStep code oracle) fuel frame).map Control.source := by
  symm
  exact eval_map _ _ Control.source (fun _ => rfl) fuel frame

theorem return_run (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request packet : List Bool) :
    TimedExecution.eval (step native code oracle machine state trace request) (3 * packet.length + 3)
      (.responding (.returned packet)) =
      PMF.pure (.source (resumed machine state trace request packet)) := by
  rw [show 3 * packet.length + 3 = (3 * packet.length + 2) + 1 by omega, TimedExecution.eval]
  simp only [step, PMF.pure_bind]
  rw [source_eval]
  unfold loading
  rw [ResponseLoading.run, PMF.pure_map]
  rfl

variable {Input : Type v} {Output : Type w}

/-- This contract is proved from physical native execution and export. Its
absorbing endpoint is used only locally, before lifting to the caller. -/
noncomputable def exported (P : Machine.Procedure Input Output) (encode : Output → List Bool)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (hTape : ∀ input output, (P.execution.exit input output).outputTape = Machine.ResponseExport.endTape (encode output))
    (read : Input → Machine.Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (cap : Input → Nat)
    (hCap : ∀ input output, output ∈ (P.execution.semantics input).support → (encode output).length ≤ cap input) :
    Procedure (Machine.ResponseExport.step P.code) Input (List Bool) :=
  Procedure.ofFixed (Machine.ResponseExport.step P.code)
    (fun input => .running (P.execution.entry input)) (fun _ packet => .returned packet)
    (fun input => (P.execution.semantics input).map encode)
    (fun input => P.execution.budget input + (3 * cap input + 4))
    (fun input => by
      rw [PMF.map_comp]
      exact Machine.ResponseExport.whole_run P encode hHalt hTape read hRead cap hCap input _ (Nat.le_refl _))

noncomputable def transfer (native : Machine.Program) (code : Code) (oracle : BitOracle State)
    (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) :
    Procedure (step native code oracle machine state trace request) (List Bool) Unit :=
  Procedure.ofFixed (step native code oracle machine state trace request)
    (fun packet => .responding (.returned packet))
    (fun packet _ => .source (resumed machine state trace request packet))
    (fun _ => PMF.pure ()) (fun packet => 3 * packet.length + 3)
    (fun packet => by simpa only [PMF.pure_map] using return_run native code oracle machine state trace request packet)

/-- Removes component post-export padding. The surrounding controller immediately
returns the packet and spends remaining time executing the resumed source. -/
noncomputable def callback (P : Machine.Procedure Input Output) (encode : Output → List Bool)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (hTape : ∀ input output, (P.execution.exit input output).outputTape = Machine.ResponseExport.endTape (encode output))
    (read : Input → Machine.Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (cap : Input → Nat)
    (hCap : ∀ input output, output ∈ (P.execution.semantics input).support → (encode output).length ≤ cap input)
    (code : Code) (oracle : BitOracle State) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool) :=
  ((exported P encode hHalt hTape read hRead cap hCap).liftBoundary exportBoundary
    (fun _ _ _ => rfl)
    (fun component h => by cases component <;> simp_all [exportBoundary, Machine.ResponseExport.step])
    (fun _ => packetRead) (fun _ _ => rfl)
    (step P.code code oracle machine state trace request) callbackBoundary Control.responding
    (fun _ => rfl)
    (fun component h => by cases component <;> simp_all [exportBoundary, step])).seq
    (transfer P.code code oracle machine state trace request)
    (fun _ _ _ => rfl) (fun input => 3 * cap input + 3)
    (fun input packet hPacket => by
      change packet ∈ ((P.execution.semantics input).map encode).support at hPacket
      rw [PMF.mem_support_map_iff] at hPacket
      obtain ⟨output, hOutput, he⟩ := hPacket
      subst packet
      have h := hCap input output hOutput
      change 3 * (encode output).length + 3 ≤ 3 * cap input + 3
      omega)

section Laws
variable (P : Machine.Procedure Input Output) (encode : Output → List Bool)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (hTape : ∀ input output, (P.execution.exit input output).outputTape = Machine.ResponseExport.endTape (encode output))
    (read : Input → Machine.Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (cap : Input → Nat)
    (hCap : ∀ input output, output ∈ (P.execution.semantics input).support → (encode output).length ≤ cap input)
    (code : Code) (oracle : BitOracle State) (machine : Machine.Configuration) (state : State)
    (trace : List (List Bool × List Bool)) (request : List Bool)

@[simp] theorem callback_budget (input : Input) :
    (callback P encode hHalt hTape read hRead cap hCap code oracle machine state trace request).budget input =
      P.execution.budget input + (6 * cap input + 7) := by
  change (P.execution.budget input + (3 * cap input + 4)) + (3 * cap input + 3) = _
  omega

/-- Marginal endpoint distribution, without erasing the real stopping costs. -/
theorem callback_distribution (input : Input) :
    ((callback P encode hHalt hTape read hRead cap hCap code oracle machine state trace request).costed input).map
      (fun result => Control.source (resumed machine state trace request result.1.1)) =
      (P.execution.semantics input).map
        (fun output => Control.source (resumed machine state trace request (encode output))) := by
  let C := callback P encode hHalt hTape read hRead cap hCap code oracle machine state trace request
  change (C.costed input).map ((fun result => Control.source (resumed machine state trace request result.1)) ∘ Prod.fst) = _
  rw [← PMF.map_comp, C.correct]
  simp only [C, callback, exported, transfer, Procedure.seq, Procedure.liftBoundary,
    Procedure.ofFixed, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

/-- Remaining time executes the source after the actual callback duration. -/
theorem callback_law (input : Input) (horizon : Nat)
    (hBudget : P.execution.budget input + (6 * cap input + 7) ≤ horizon) :
    TimedExecution.eval (step P.code code oracle machine state trace request) horizon
      (.responding (.running (P.execution.entry input))) =
      ((callback P encode hHalt hTape read hRead cap hCap code oracle machine state trace request).costed input).bind
        (fun result => TimedExecution.eval (step P.code code oracle machine state trace request)
          (horizon - result.2) (.source (resumed machine state trace request result.1.1))) := by
  exact (callback P encode hHalt hTape read hRead cap hCap code oracle machine state trace request).law input horizon
    (by rw [callback_budget]; exact hBudget)

end Laws
end CryptoOracle.Interactive.NativeCallback
