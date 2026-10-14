import Foundation.Constructions.Hash.NativeSimulatorKeyProtect

/-! Terminal acceptance, runtime fuel, protected original-key save, empty
suffix initialization, and reconstruction execute under one finite code. -/
namespace Foundation.Hash.Native.SimulatorTerminalReconstruct
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n κ : Nat}

def tail (initial : Bits n) (κ : Nat) : Code :=
  SimulatorKeyProtect.code n κ (SimulatorReconstruct.code initial κ)
def code (initial : Bits n) (terminal : Bits κ) (rejected : Code) : Code :=
  SimulatorTerminalFuel.code terminal n (tail initial κ) rejected
def counterPrefix (initial : Bits n) (terminal : Bits κ) : Code :=
  CodeRelocation.host (SimulatorTerminalFuel.guardPrefix terminal (SimulatorTerminalFuel.body n κ (tail initial κ)))
    (SimulatorTerminalFuel.body n κ [])
def steps (table : CompressionTable (Bits κ) (Bits n)) : Nat :=
  SimulatorTerminalFuel.steps table + (11 * n + 12 * κ + 6 * table.length + 26) +
    SimulatorReconstruct.budget table table.length 0

theorem code_host (initial : Bits n) (terminal : Bits κ) (rejected : Code) :
    code initial terminal rejected = CodeRelocation.host (counterPrefix initial terminal)
      (CodeRelocation.host (tail initial κ) rejected) := by
  rw [code, SimulatorTerminalFuel.code, SimulatorTerminalFuel.guard_host, SimulatorTerminalFuel.body_link,
    CodeRelocation.host_assoc, ← CodeRelocation.host_assoc, ← SimulatorTerminalFuel.body_link]; rfl

theorem code_length (initial : Bits n) (terminal : Bits κ) (rejected : Code) :
    (code initial terminal rejected).length = 31 * n + 33 * κ + 131 + rejected.length := by
  rw [code, SimulatorTerminalFuel.code_length, tail, SimulatorKeyProtect.code_length, SimulatorReconstruct.code_length]
  omega

theorem code_native (initial : Bits n) (terminal : Bits κ) (rejected : Code)
    (hr : ∀ op ∈ rejected, ∃ native, op = .native native) :
    ∀ op ∈ code initial terminal rejected, ∃ native, op = .native native :=
  SimulatorTerminalFuel.code_native _ _ _ _
    (SimulatorKeyProtect.code_native _ _ _ (SimulatorReconstruct.code_native _ _)) hr

/-- Both success and reconstruction failure stop with the original key saved.
The native interpreter never exits into appended rejection code on this path. -/
theorem accepted_law (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial target : Bits n) (terminal : Bits κ)
    (rejected : Code) (table : CompressionTable (Bits κ) (Bits n)) :
    (TimedExecution.eval (Reification.timedStep (code initial terminal rejected) oracle) (steps table)
      (NativeCode.frame state trace (SimulatorTerminalFuel.flagStart target terminal table))).map
      (SimulatorKeyProtect.view (SimulatorKeyProtect.width n κ) κ) =
      PMF.pure (some (state, trace, true, compressionPacket (target, (true, terminal)),
        terminalMessage initial terminal table (target, (true, terminal)))) := by
  let query : CompressionInput (Bits κ) (Bits n) := (target, (true, terminal))
  let time := (11 * n + 12 * κ + 6 * table.length + 26) + SimulatorReconstruct.budget table table.length 0
  have hl := SimulatorKeyProtect.with_reconstruct_law oracle state trace initial table.length query table
  have ha := CodePrefixExecution.append_running_final (tail initial κ)
    (rejected.map (CodeRelocation.instruction (tail initial κ).length)) oracle time
    (NativeCode.frame state trace (SimulatorKeyProtect.start table table.length query))
    (by
      intro out hs
      have hm : SimulatorKeyProtect.view (SimulatorKeyProtect.width n κ) κ out ∈
          ((TimedExecution.eval (Reification.timedStep (tail initial κ) oracle) time
            (NativeCode.frame state trace (SimulatorKeyProtect.start table table.length query))).map
            (SimulatorKeyProtect.view (SimulatorKeyProtect.width n κ) κ)).support :=
        by rw [PMF.mem_support_map_iff]; exact ⟨out, hs, rfl⟩
      change SimulatorKeyProtect.view _ _ out ∈ (TimedExecution.eval (Reification.timedStep (SimulatorKeyProtect.code n κ (SimulatorReconstruct.code initial κ)) oracle) _ _ |>.map _).support at hm
      rw [hl, PMF.mem_support_pure_iff] at hm
      cases hc : out.control <;> simp_all [SimulatorKeyProtect.view, CodePrefixExecution.exited])
  have hp := SimulatorTerminalFuel.accepted_run oracle state trace (tail initial κ) rejected target terminal table
  have hp' : TimedExecution.eval (Reification.timedStep (code initial terminal rejected) oracle) (SimulatorTerminalFuel.steps table)
      (NativeCode.frame state trace (SimulatorTerminalFuel.flagStart target terminal table)) =
      PMF.pure (CodeRelocation.frame (counterPrefix initial terminal).length
        (NativeCode.frame state trace (SimulatorKeyProtect.start table table.length query))) := by
    simpa only [code, SimulatorTerminalFuel.steps, counterPrefix, CodeRelocation.code_length,
      SimulatorKeyProtect.start, SimulatorFuelPrepare.finish, SimulatorTerminalFuel.queryCells, query] using hp
  rw [steps, show SimulatorTerminalFuel.steps table + (11 * n + 12 * κ + 6 * table.length + 26) +
      SimulatorReconstruct.budget table table.length 0 = SimulatorTerminalFuel.steps table + time from by dsimp [time]; omega,
    TimedExecution.eval_add, hp', PMF.pure_bind, code_host, CodeRelocation.eval, PMF.map_comp,
    SimulatorKeyProtect.view_frame, CodeRelocation.host, ha]
  simpa only [tail, time, query, terminalMessage, and_self, ↓reduceIte] using hl

/-- The joint observation identifies an actual halted machine frame with
unchanged opaque state/history, a recoverable saved key, and the correct message. -/
theorem stopped_key (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial target : Bits n) (terminal : Bits κ)
    (rejected : Code) (table : CompressionTable (Bits κ) (Bits n)) (out : Configuration State)
    (hs : out ∈ (TimedExecution.eval (Reification.timedStep (code initial terminal rejected) oracle) (steps table)
      (NativeCode.frame state trace (SimulatorTerminalFuel.flagStart target terminal table))).support) :
    ∃ machine, out = NativeCode.frame state trace machine ∧ machine.halted = true ∧
      machine.inputTape.bits.take (SimulatorKeyProtect.width n κ) = compressionPacket (target, (true, terminal)) ∧
      SimulatorReconstruct.readResult κ machine = terminalMessage initial terminal table (target, (true, terminal)) := by
  have hm : SimulatorKeyProtect.view (SimulatorKeyProtect.width n κ) κ out ∈
      ((TimedExecution.eval (Reification.timedStep (code initial terminal rejected) oracle) (steps table)
        (NativeCode.frame state trace (SimulatorTerminalFuel.flagStart target terminal table))).map
        (SimulatorKeyProtect.view (SimulatorKeyProtect.width n κ) κ)).support := by
    rw [PMF.mem_support_map_iff]; exact ⟨out, hs, rfl⟩
  rw [accepted_law, PMF.mem_support_pure_iff] at hm
  rcases out with ⟨actualState, control, actualTrace⟩
  cases control <;> simp only [SimulatorKeyProtect.view] at hm
  case running machine =>
    have he := Option.some.inj hm
    have hstate := congrArg Prod.fst he
    have htrace := congrArg (fun x => x.2.1) he
    have hhalt := congrArg (fun x => x.2.2.1) he
    have hkey := congrArg (fun x => x.2.2.2.1) he
    have hread := congrArg (fun x => x.2.2.2.2) he
    dsimp at hstate htrace hhalt hkey hread
    subst actualState
    subst actualTrace
    exact ⟨machine, rfl, hhalt, hkey, hread⟩
  all_goals cases hm

theorem encoded_peak (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (initial target : Bits n) (terminal : Bits κ) (table : CompressionTable (Bits κ) (Bits n)) (elapsed : Nat)
    (within : elapsed ≤ steps table) (out : Configuration State)
    (supported : out ∈ (TimedExecution.eval (Reification.timedStep (code initial terminal [.native .halt]) oracle) elapsed
      (NativeCode.frame state trace (SimulatorTerminalFuel.flagStart target terminal table))).support) :
    ((NativeCode.fullEncoding E).encode (code initial terminal [.native .halt], out)).length ≤
      NativeCode.storageBound (code initial terminal [.native .halt])
        (NativePacketComponent.Resources.frameSize stateSize (NativeCode.frame state trace (SimulatorTerminalFuel.flagStart target terminal table))) (steps table) :=
  NativeCode.encoded_peak E stateSize hState oracle state trace _
    (code_native _ _ _ (by intro op hm; exact ⟨_, by simpa using hm⟩)) _ _ elapsed within out supported

end Foundation.Hash.Native.SimulatorTerminalReconstruct
