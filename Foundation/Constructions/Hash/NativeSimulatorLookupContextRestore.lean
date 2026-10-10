import Foundation.Constructions.Hash.NativeSimulatorLookupRestore

/-! Execute the existing lookup/rewind code from a represented blank separator.
The separator and arbitrary cells beyond it survive exactly. This provides
physical reusable-table entries; it does not load a new query or implement
terminal recognition. -/
namespace Foundation.Hash.Native.SimulatorLookupContextRestore
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev code := SimulatorLookupRestore.code
abbrev rewindSteps := @SimulatorLookupRestore.rewindSteps
abbrev steps := @SimulatorLookupRestore.steps

def rewindInput {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (saved beforeOutput : List (Option Bool)) :
    NativeBitstringRewind.Scratch.Input where
  bits := (SimulatorLookup.lookupSplit query table).1
  current := (Tape.ofBits (SimulatorLookup.lookupSplit query table).2).current
  right := (Tape.ofBits (SimulatorLookup.lookupSplit query table).2).right
  other := (SimulatorLookup.lookupFinish query table (none :: saved) beforeOutput).outputTape
  saved := saved

theorem entry {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (saved beforeOutput : List (Option Bool)) :
    (SimulatorLookup.lookupFinish query table (none :: saved) beforeOutput).resumeAt 0 =
      NativeBitstringRewind.Scratch.initial (rewindInput query table saved beforeOutput) := by
  simp only [Configuration.resumeAt, NativeBitstringRewind.Scratch.initial, rewindInput,
    SimulatorLookup.lookupFinish_input]

def finish {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (saved beforeOutput : List (Option Bool)) : Configuration State :=
  CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length
    (NativeCode.frame state trace (NativeBitstringRewind.Scratch.finish (rewindInput query table saved beforeOutput)))

theorem rewind_first_joint {State : Type*} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (input : NativeBitstringRewind.Scratch.Input) :
    runToBoundary (Reification.timedStep (NativeCode.code rewindBitstring) oracle)
      (fun frame => Reification.terminal frame.control) (2 * input.bits.length + 4)
      (NativeCode.frame state trace (NativeBitstringRewind.Scratch.initial input)) =
      PMF.pure (NativeCode.frame state trace (NativeBitstringRewind.Scratch.finish input), 2 * input.bits.length + 4) := by
  have actual := NativeBitstringRewind.Scratch.trace input
  have costed := NativeBitstringRewind.Scratch.component.firstArrival_costed_of_trace input _ _ actual
    rewindBitstring_no_randomBit rfl (Nat.le_refl _)
  have h := NativeCode.first_joint NativeBitstringRewind.Scratch.component oracle state trace input
  rw [costed, PMF.pure_map] at h
  exact h

theorem lookup_return {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (saved beforeOutput : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (SimulatorLookup.lookupSteps query table)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query (none :: saved) beforeOutput)) =
      PMF.pure (CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length
        (NativeCode.frame state trace (NativeBitstringRewind.Scratch.initial (rewindInput query table saved beforeOutput)))) := by
  change TimedExecution.eval (Reification.timedStep (SimulatorLookup.lookupHost n κ (NativeCode.code rewindBitstring)) oracle) _ _ = _
  rw [SimulatorLookup.lookup_return_run]
  have layout := entry query table saved beforeOutput
  rw [← layout]
  simp [NativeCode.frame, CodeRelocation.frame, CodeRelocation.control, Configuration.resumeAt, Configuration.rebasePc]

/-- A real lookup-return jump is followed by the existing native rewind.
Neither the endpoint table nor the exact first-halt cost is assumed. -/
theorem first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (saved beforeOutput : List (Option Bool)) :
    runToBoundary (Reification.timedStep (code n κ) oracle) (fun frame => Reification.terminal frame.control)
      (steps query table) (NativeCode.frame state trace (SimulatorLookup.scanStart table query (none :: saved) beforeOutput)) =
      PMF.pure (finish state trace query table saved beforeOutput, steps query table) := by
  have prefixLaw := runToBoundary_joint_of_active_final (Reification.timedStep (code n κ) oracle)
    (fun frame => Reification.terminal frame.control)
    (by intro frame terminal; simp [Reification.timedStep, terminal])
    (SimulatorLookup.lookupSteps query table)
    (NativeCode.frame state trace (SimulatorLookup.scanStart table query (none :: saved) beforeOutput))
    (by intro frame support
        rw [lookup_return, PMF.mem_support_pure_iff] at support
        subst frame
        rfl)
  rw [lookup_return, PMF.pure_map] at prefixLaw
  rw [steps, SimulatorLookupRestore.steps, runToBoundary_add, prefixLaw, PMF.pure_bind]
  have bodyLaw := runToBoundary_map
    (Reification.timedStep (NativeCode.code rewindBitstring) oracle)
    (Reification.timedStep (code n κ) oracle)
    (fun frame => Reification.terminal frame.control) (fun frame => Reification.terminal frame.control)
    (CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length)
    (fun frame => CodeRelocation.terminal _ frame.control)
    (fun frame active => by
      simpa only [code, SimulatorLookupRestore.code, SimulatorLookup.lookupHost, HaltReturn.host, CodeRelocation.host, List.length_map] using
        (CodeRelocation.timed_step ((SimulatorLookup.lookupCode n κ).map (HaltReturn.instruction (SimulatorLookup.lookupCode n κ).length))
          (NativeCode.code rewindBitstring) oracle frame))
    (rewindSteps query table)
    (NativeCode.frame state trace (NativeBitstringRewind.Scratch.initial (rewindInput query table saved beforeOutput)))
  rw [bodyLaw]
  have rewindLaw := rewind_first_joint oracle state trace (rewindInput query table saved beforeOutput)
  change runToBoundary _ _ (rewindSteps query table) _ = _ at rewindLaw
  rw [rewindLaw, PMF.pure_map, PMF.pure_map]
  rfl

theorem run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (saved beforeOutput : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps query table)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query (none :: saved) beforeOutput)) =
      PMF.pure (finish state trace query table saved beforeOutput) := by
  rw [runToBoundary_law (Reification.timedStep (code n κ) oracle)
    (fun frame => Reification.terminal frame.control) (steps query table) (steps query table)
    _ (Nat.le_refl _), first_joint, PMF.pure_bind]
  simp [TimedExecution.eval]

theorem finish_table {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (saved beforeOutput : List (Option Bool)) :
    (match (finish state trace query table saved beforeOutput).control with
      | .running machine => some machine.inputTape | _ => none) =
      some ({ Tape.ofBits (SimulatorLookup.tableBits table) with left := none :: saved }) := by
  change some (NativeBitstringRewind.Scratch.finish (rewindInput query table saved beforeOutput)).inputTape = _
  apply congrArg some
  have nonempty := SimulatorLookup.lookupSplit_unread_nonempty query table
  have layout := SimulatorLookup.lookupSplit_table query table
  generalize hPrefix : (SimulatorLookup.lookupSplit query table).1 = leading at *
  generalize hUnread : (SimulatorLookup.lookupSplit query table).2 = unread at *
  simp only [NativeBitstringRewind.Scratch.finish, rewindInput, hPrefix, hUnread]
  rw [← layout]
  cases unread with
  | nil => exact False.elim (nonempty rfl)
  | cons bit rest => cases leading <;> simp [Tape.ofBits, Tape.moveRight, List.map_append]

/-- One blank left by a cache hit is a valid entry separator, without
normalization or deletion. Arbitrary older cells remain beyond it. -/
theorem restored_entry {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (saved beforeOutput : List (Option Bool)) :
    (SimulatorLookup.scanStart table query (none :: saved) beforeOutput).inputTape =
      { Tape.ofBits (SimulatorLookup.tableBits table) with left := none :: saved } := rfl

/-- The same bound as the empty-context execution: saved cells are not scanned. -/
theorem steps_le {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) :
    steps query table ≤ table.length * (15 * n + 12 * κ + 26) + 12 * n + 7 * κ + 23 :=
  SimulatorLookupRestore.steps_le query table

theorem encoded_peak {State : Type*} {n κ : Nat}
    (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (saved beforeOutput : List (Option Bool)) (elapsed : Nat) (within : elapsed ≤ steps query table)
    (target : Configuration State)
    (support : target ∈ (TimedExecution.eval (Reification.timedStep (code n κ) oracle) elapsed
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query (none :: saved) beforeOutput))).support) :
    ((NativeCode.fullEncoding E).encode (code n κ, target)).length ≤
      NativeCode.storageBound (code n κ)
        (NativePacketComponent.Resources.frameSize stateSize
          (NativeCode.frame state trace (SimulatorLookup.scanStart table query (none :: saved) beforeOutput)))
        (steps query table) := by
  exact NativeCode.encoded_peak E stateSize hState oracle state trace (code n κ)
    (SimulatorLookupRestore.code_native n κ) _ (steps query table) elapsed within target support

abbrev Input (State : Type*) (n κ : Nat) :=
  { input : SimulatorLookup.LookupInput State n κ // ∃ saved, input.beforeInput = none :: saved }

theorem input_before {State : Type*} {n κ : Nat} (input : Input State n κ) :
    input.val.beforeInput = none :: input.val.beforeInput.tail := by
  obtain ⟨saved, h⟩ := input.property
  simp [h]

/-- Register the physical represented-separator entry using the existing
lookup input type. The actual saved prefix is passed through, not replaced. -/
noncomputable def procedure {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure (Reification.timedStep (code n κ) oracle) (Input State n κ) (Configuration State) :=
  Procedure.ofFixed _
    (fun input => NativeCode.frame input.val.state input.val.trace
      (SimulatorLookup.scanStart input.val.table input.val.query input.val.beforeInput input.val.beforeOutput))
    (fun _ output => output)
    (fun input => PMF.pure (finish input.val.state input.val.trace input.val.query input.val.table
      input.val.beforeInput.tail input.val.beforeOutput))
    (fun input => steps input.val.query input.val.table)
    (fun input => by rw [input_before input, run, PMF.pure_map]; rfl)

theorem procedure_operational {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure.Operational (procedure n κ oracle) := by
  apply Procedure.operational_ofFixed

theorem procedure_first_joint {State : Type*} (n κ : Nat) (oracle : BitOracle State)
    (input : Input State n κ) :
    runToBoundary (Reification.timedStep (code n κ) oracle)
      (fun frame => Reification.terminal frame.control)
      ((procedure n κ oracle).budget input) ((procedure n κ oracle).entry input) =
      (procedure n κ oracle).costed input := by
  change runToBoundary _ _ (steps input.val.query input.val.table)
    (NativeCode.frame input.val.state input.val.trace
      (SimulatorLookup.scanStart input.val.table input.val.query input.val.beforeInput input.val.beforeOutput)) = _
  rw [input_before input, first_joint]
  simp only [procedure, TimedExecution.Procedure.ofFixed, PMF.pure_map]

end Foundation.Hash.Native.SimulatorLookupContextRestore
