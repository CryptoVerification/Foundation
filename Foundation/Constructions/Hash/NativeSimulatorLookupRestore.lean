import Foundation.Constructions.Hash.NativeSimulatorLookupSplit
import Foundation.Constructions.Hash.NativeSimulatorLookupReturn
import Foundation.Crypto.Semantics.Oracle.NativeCodeResources

/-! One actual call executes the original sequential lookup and restores the
input-table head, retaining all table bits and the lookup response. This
component prepares reusable table access; it does not prepare a next request
or implement terminal recognition. -/
namespace Foundation.Hash.Native.SimulatorLookupRestore
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def code (n κ : Nat) : Code := SimulatorLookup.lookupHost n κ (NativeCode.code rewindBitstring)

theorem code_length (n κ : Nat) : (code n κ).length = 10 * n + 2 * κ + 82 := by
  simp [code, SimulatorLookup.lookupHost_length, NativeCode.code, rewindBitstring]; omega

theorem code_native (n κ : Nat) : ∀ op ∈ code n κ, ∃ native, op = .native native := by
  apply HaltReturn.host_native _ _ (SimulatorLookup.lookupCode_native n κ)
  intro op member
  simp only [NativeCode.code, List.mem_map] at member
  obtain ⟨native, _, rfl⟩ := member
  exact ⟨_, rfl⟩

def rewindSteps {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) := 2 * (SimulatorLookup.lookupSplit query table).1.length + 4

def steps {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) := SimulatorLookup.lookupSteps query table + rewindSteps query table

def finish {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) : Configuration State :=
  CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length
    (NativeCode.frame state trace (NativeBitstringRewind.finish (SimulatorLookup.lookupRewindInput query table beforeOutput)))

/-- The source component's existing trace determines its actual first halt,
with arbitrary current/unread cells and the complete other tape. -/
theorem rewind_first_joint {State : Type*} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (input : NativeBitstringRewind.Input) :
    runToBoundary (Reification.timedStep (NativeCode.code rewindBitstring) oracle)
      (fun frame => Reification.terminal frame.control) (2 * input.bits.length + 4)
      (NativeCode.frame state trace (NativeBitstringRewind.initial input)) =
      PMF.pure (NativeCode.frame state trace (NativeBitstringRewind.finish input), 2 * input.bits.length + 4) := by
  have actual := rewindBitstring_runs_from input.bits input.current input.right input.other
  have costed := NativeBitstringRewind.component.firstArrival_costed_of_trace input _ _ actual
    rewindBitstring_no_randomBit rfl (Nat.le_refl _)
  have h := NativeCode.first_joint NativeBitstringRewind.component oracle state trace input
  rw [costed, PMF.pure_map] at h
  exact h

theorem lookup_return {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (SimulatorLookup.lookupSteps query table)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      PMF.pure (CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length
        (NativeCode.frame state trace (NativeBitstringRewind.initial (SimulatorLookup.lookupRewindInput query table beforeOutput)))) := by
  unfold code
  rw [SimulatorLookup.lookup_return_run]
  have layout := SimulatorLookup.lookupRewind_entry query table beforeOutput
  rw [← layout]
  simp [NativeCode.frame, CodeRelocation.frame, CodeRelocation.control, Configuration.resumeAt, Configuration.rebasePc]

/-- A real lookup-return jump is followed by the existing native rewind.
Neither the endpoint table nor the exact first-halt cost is assumed. -/
theorem first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    runToBoundary (Reification.timedStep (code n κ) oracle) (fun frame => Reification.terminal frame.control)
      (steps query table) (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      PMF.pure (finish state trace query table beforeOutput, steps query table) := by
  have prefixLaw := runToBoundary_joint_of_active_final (Reification.timedStep (code n κ) oracle)
    (fun frame => Reification.terminal frame.control)
    (by intro frame terminal; simp [Reification.timedStep, terminal])
    (SimulatorLookup.lookupSteps query table)
    (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))
    (by intro frame support
        rw [lookup_return, PMF.mem_support_pure_iff] at support
        subst frame
        rfl)
  rw [lookup_return, PMF.pure_map] at prefixLaw
  rw [steps, runToBoundary_add, prefixLaw, PMF.pure_bind]
  have bodyLaw := runToBoundary_map
    (Reification.timedStep (NativeCode.code rewindBitstring) oracle)
    (Reification.timedStep (code n κ) oracle)
    (fun frame => Reification.terminal frame.control) (fun frame => Reification.terminal frame.control)
    (CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length)
    (fun frame => CodeRelocation.terminal _ frame.control)
    (fun frame active => by
      simpa only [code, SimulatorLookup.lookupHost, HaltReturn.host, CodeRelocation.host, List.length_map] using
        (CodeRelocation.timed_step ((SimulatorLookup.lookupCode n κ).map (HaltReturn.instruction (SimulatorLookup.lookupCode n κ).length))
          (NativeCode.code rewindBitstring) oracle frame))
    (rewindSteps query table)
    (NativeCode.frame state trace (NativeBitstringRewind.initial (SimulatorLookup.lookupRewindInput query table beforeOutput)))
  rw [bodyLaw]
  have rewindLaw := rewind_first_joint oracle state trace (SimulatorLookup.lookupRewindInput query table beforeOutput)
  change runToBoundary _ _ (rewindSteps query table) _ = _ at rewindLaw
  rw [rewindLaw, PMF.pure_map, PMF.pure_map]
  rfl

theorem run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps query table)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      PMF.pure (finish state trace query table beforeOutput) := by
  rw [runToBoundary_law (Reification.timedStep (code n κ) oracle)
    (fun frame => Reification.terminal frame.control) (steps query table) (steps query table)
    _ (Nat.le_refl _), first_joint, PMF.pure_bind]
  simp [TimedExecution.eval]

/-- Width and table-size bound for the whole lookup plus physical rewind. -/
theorem steps_le {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) :
    steps query table ≤ table.length * (15 * n + 12 * κ + 26) + 12 * n + 7 * κ + 23 := by
  have lookupBound := SimulatorLookup.lookupSteps_le query table
  rw [SimulatorLookup.lookupBudget_eq] at lookupBound
  have rewindBound := SimulatorLookup.lookupSplit_prefix_length query table
  have bound : SimulatorLookup.lookupSteps query table +
      2 * (SimulatorLookup.lookupSplit query table).1.length + 4 ≤
      table.length * (9 * n + 8 * κ + 18) + 12 * n + 7 * κ + 19 +
      2 * (table.length * (3 * n + 2 * κ + 4)) + 4 := by omega
  have size : table.length * (9 * n + 8 * κ + 18) + 12 * n + 7 * κ + 19 +
      2 * (table.length * (3 * n + 2 * κ + 4)) + 4 =
      table.length * (15 * n + 12 * κ + 26) + 12 * n + 7 * κ + 23 := by ring
  rw [size] at bound
  simpa only [steps, rewindSteps, Nat.add_assoc] using bound

/-- All intermediate physical frames, including the actual lookup-return
jump and both tapes during rewind, retain the native encoded-storage bound. -/
theorem encoded_peak {State : Type*} {n κ : Nat}
    (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (elapsed : Nat) (within : elapsed ≤ steps query table)
    (target : Configuration State)
    (support : target ∈ (TimedExecution.eval (Reification.timedStep (code n κ) oracle) elapsed
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))).support) :
    ((NativeCode.fullEncoding E).encode (code n κ, target)).length ≤
      NativeCode.storageBound (code n κ)
        (NativePacketComponent.Resources.frameSize stateSize
          (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput))) (steps query table) := by
  exact NativeCode.encoded_peak E stateSize hState oracle state trace (code n κ) (code_native n κ)
    _ (steps query table) elapsed within target support

/-- Register with the existing composable procedure interface. The subtype
requires the physical blank boundary needed by the rewind scan. -/
noncomputable def procedure {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure (Reification.timedStep (code n κ) oracle)
      { input : SimulatorLookup.LookupInput State n κ // input.beforeInput = [] } (Configuration State) :=
  Procedure.ofFixed _
    (fun input => NativeCode.frame input.val.state input.val.trace
      (SimulatorLookup.scanStart input.val.table input.val.query [] input.val.beforeOutput))
    (fun _ output => output)
    (fun input => PMF.pure (finish input.val.state input.val.trace input.val.query input.val.table input.val.beforeOutput))
    (fun input => steps input.val.query input.val.table)
    (fun input => by rw [run, PMF.pure_map])

theorem procedure_operational {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure.Operational (procedure n κ oracle) := by
  apply Procedure.operational_ofFixed

theorem procedure_first_joint {State : Type*} (n κ : Nat) (oracle : BitOracle State)
    (input : { input : SimulatorLookup.LookupInput State n κ // input.beforeInput = [] }) :
    runToBoundary (Reification.timedStep (code n κ) oracle)
      (fun frame => Reification.terminal frame.control)
      ((procedure n κ oracle).budget input) ((procedure n κ oracle).entry input) =
      (procedure n κ oracle).costed input := by
  change runToBoundary _ _ (steps input.val.query input.val.table)
    (NativeCode.frame input.val.state input.val.trace
      (SimulatorLookup.scanStart input.val.table input.val.query [] input.val.beforeOutput)) = _
  rw [first_joint]
  simp only [procedure, TimedExecution.Procedure.ofFixed, PMF.pure_map]

theorem finish_table {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    (match (finish state trace query table beforeOutput).control with
      | .running machine => some machine.inputTape | _ => none) =
      some ({ Tape.ofBits (SimulatorLookup.tableBits table) with left := [none] }) := by
  exact congrArg some (SimulatorLookup.lookupRewind_table query table beforeOutput)

theorem finish_output {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    (match (finish state trace query table beforeOutput).control with
      | .running machine => some machine.outputTape | _ => none) =
      some (SimulatorLookup.lookupFinish query table [] beforeOutput).outputTape := rfl

/-- A compiled return from rewind, followed by arbitrary native or
interactive code. The body receives exactly the retained physical tapes. -/
def codeWithBody (n κ : Nat) (body : Code) : Code :=
  SimulatorLookup.lookupHost n κ (CodeRelocation.host (NativeCode.subroutinePrefix rewindBitstring) body)

theorem codeWithBody_length (n κ : Nat) (body : Code) :
    (codeWithBody n κ body).length = 10 * n + 2 * κ + 83 + body.length := by
  simp [codeWithBody, SimulatorLookup.lookupHost_length, CodeRelocation.code_length,
    NativeCode.subroutinePrefix_length, rewindBitstring]; omega

theorem codeWithBody_native (n κ : Nat) (body : Code)
    (native : ∀ op ∈ body, ∃ instruction, op = .native instruction) :
    ∀ op ∈ codeWithBody n κ body, ∃ instruction, op = .native instruction := by
  apply HaltReturn.host_native _ _ (SimulatorLookup.lookupCode_native n κ)
  apply CodeRelocation.host_native _ _ _ native
  intro op member
  simp only [NativeCode.subroutinePrefix, NativeCode.code, List.mem_map] at member
  obtain ⟨instruction, _, rfl⟩ := member
  exact ⟨_, rfl⟩

def afterRewind {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) : Machine.Configuration :=
  (NativeBitstringRewind.finish (SimulatorLookup.lookupRewindInput query table beforeOutput)).resumeAt 0

theorem body_rewind_run {State : Type*} {n κ : Nat}
    (body : Code) (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep
      (CodeRelocation.host (NativeCode.subroutinePrefix rewindBitstring) body) oracle)
      (rewindSteps query table)
      (NativeCode.frame state trace (NativeBitstringRewind.initial (SimulatorLookup.lookupRewindInput query table beforeOutput))) =
      PMF.pure (CodeRelocation.frame 5 (NativeCode.frame state trace (afterRewind query table beforeOutput))) := by
  let input := SimulatorLookup.lookupRewindInput query table beforeOutput
  have actual := rewindBitstring_runs_from input.bits input.current input.right input.other
  have costed := NativeBitstringRewind.component.firstArrival_costed_of_trace input _ _ actual
    rewindBitstring_no_randomBit rfl (Nat.le_refl _)
  have first := NativeCode.subroutine_first_joint NativeBitstringRewind.component
    (body.map (CodeRelocation.instruction 5)) oracle state trace input
  rw [costed, PMF.pure_map] at first
  change runToBoundary (Reification.timedStep
    (NativeCode.subroutinePrefix rewindBitstring ++ body.map (CodeRelocation.instruction 5)) oracle)
    (NativeCode.returnBoundary 5) (rewindSteps query table)
    (NativeCode.frame state trace (NativeBitstringRewind.initial input)) =
    PMF.pure (NativeCode.frame state trace ((NativeBitstringRewind.finish input).resumeAt 5),
      rewindSteps query table) at first
  have law : runToBoundary (Reification.timedStep
      (CodeRelocation.host (NativeCode.subroutinePrefix rewindBitstring) body) oracle)
      (NativeCode.returnBoundary 5) (rewindSteps query table)
      (NativeCode.frame state trace (NativeBitstringRewind.initial input)) =
      PMF.pure (CodeRelocation.frame 5 (NativeCode.frame state trace (afterRewind query table beforeOutput)),
        rewindSteps query table) := by
    simpa only [input, CodeRelocation.host, show (NativeCode.subroutinePrefix rewindBitstring).length = 5 by
      simp [NativeCode.subroutinePrefix_length, rewindBitstring], afterRewind,
      Configuration.resumeAt, Configuration.rebasePc, NativeCode.frame, CodeRelocation.frame, CodeRelocation.control,
      Nat.add_zero] using first
  rw [runToBoundary_law _ (NativeCode.returnBoundary 5) (rewindSteps query table)
    (rewindSteps query table) _ (Nat.le_refl _), law, PMF.pure_bind]
  simp [TimedExecution.eval]

/-- Whole original lookup and physical rewind, then the actual relocated
body. No intermediate host resume or replacement of any tape is executed. -/
theorem withBody_run {State : Type*} {n κ : Nat}
    (body : Code) (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fuel : Nat) :
    TimedExecution.eval (Reification.timedStep (codeWithBody n κ body) oracle)
      (steps query table + fuel)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      (TimedExecution.eval (Reification.timedStep body oracle) fuel
        (NativeCode.frame state trace (afterRewind query table beforeOutput))).map
          (fun frame => CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length (CodeRelocation.frame 5 frame)) := by
  have entry : NativeCode.frame state trace
      ((SimulatorLookup.lookupFinish query table [] beforeOutput).resumeAt (SimulatorLookup.lookupCode n κ).length) =
      CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length
        (NativeCode.frame state trace (NativeBitstringRewind.initial (SimulatorLookup.lookupRewindInput query table beforeOutput))) := by
    rw [← SimulatorLookup.lookupRewind_entry query table beforeOutput]
    simp [NativeCode.frame, CodeRelocation.frame, CodeRelocation.control, Configuration.resumeAt, Configuration.rebasePc]
  have returned := SimulatorLookup.lookup_return_run
    (CodeRelocation.host (NativeCode.subroutinePrefix rewindBitstring) body)
    oracle state trace query table [] beforeOutput
  rw [entry] at returned
  unfold steps codeWithBody
  rw [Nat.add_assoc, TimedExecution.eval_add, returned, PMF.pure_bind]
  unfold SimulatorLookup.lookupHost
  rw [HaltReturn.body_eval, TimedExecution.eval_add, body_rewind_run, PMF.pure_bind]
  have placed := CodeRelocation.eval (NativeCode.subroutinePrefix rewindBitstring) body oracle fuel
    (NativeCode.frame state trace (afterRewind query table beforeOutput))
  change TimedExecution.eval _ fuel (CodeRelocation.frame 5 _) = _ at placed
  rw [placed, PMF.map_comp]
  rfl

end Foundation.Hash.Native.SimulatorLookupRestore
