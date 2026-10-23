import Foundation.Constructions.Hash.NativeOracleExecution
import Foundation.Constructions.Symmetric.RandomFunctionMACNativeInterface
import Foundation.Crypto.Semantics.Oracle.NativeCompactRequest
import Foundation.Crypto.Semantics.Oracle.CodePrefixExecution

/-! The existing native cache backend entered from the SAME MAC's compact
request. The private machine is retained across loading, padding and lookup.
All native phases use one fixed extended program. This file reaches the
actual native halt; physical response export and caller resumption are
separate obligations, not replaced by the mathematical observation below.
-/
namespace Foundation.Hash.Native.CompactMACQuery
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
open Foundation.Symmetric.RandomFunctionMACNativeCaller
set_option backward.isDefEq.respectTransparency false

abbrev source : Code := SimulatorDispatchQueryLoading.code 8 0
abbrev entry : Nat := SimulatorLookup.headerPc 8 0
def code : Code := NativeCompactRequest.code source entry

noncomputable def step {State : Type} (oracle : BitOracle State) :
    SimulatorQueryLoading.Control State → PMF (SimulatorQueryLoading.Control State)
  | .admitting state machine trace request =>
      PMF.pure (.executing ⟨state, .loading (machine.resumeAt source.length) request {}, trace⟩)
  | .executing frame => (Reification.timedStep code oracle frame).map .executing

theorem executing_run {State : Type} (oracle : BitOracle State) (fuel : Nat) (frame : Configuration State) :
    TimedExecution.eval (step oracle) fuel (.executing frame) =
      (TimedExecution.eval (Reification.timedStep code oracle) fuel frame).map .executing := by
  induction fuel generalizing frame with
  | zero => simp [TimedExecution.eval, PMF.pure_map]
  | succ fuel ih => simp only [TimedExecution.eval, step, PMF.bind_map, PMF.map_bind, ih, Function.comp_def]

theorem prepare_run {State : Type} (oracle : BitOracle State) (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (message : Message) :
    TimedExecution.eval (step oracle) 41 (.admitting state machine trace (encodeMessage message)) =
      PMF.pure (.executing (SimulatorQueryLoading.loadedFrame 8 0 state machine trace (Backend.request message))) := by
  obtain ⟨first, second, third, raw⟩ : ∃ first second third, encodeMessage message = [first, second, third] := by
    exact ⟨_, _, _, rfl⟩
  have admission : TimedExecution.eval (step oracle) 1 (.admitting state machine trace (encodeMessage message)) =
      PMF.pure (.executing (⟨state, .loading (machine.resumeAt source.length) (encodeMessage message) {}, trace⟩ : Configuration State)) := by
    simp [TimedExecution.eval, step]
  have loaded : TimedExecution.eval (Reification.timedStep code oracle) 40
      (⟨state, .loading (machine.resumeAt source.length) (encodeMessage message) {}, trace⟩ : Configuration State) =
      PMF.pure (SimulatorQueryLoading.loadedFrame 8 0 state machine trace (Backend.request message)) := by
    simpa only [code, entry, raw, Backend.request_eq, NativeCompactRequest.finish,
      SimulatorQueryLoading.loadedFrame, NativeCode.frame, Machine.Configuration.resumeAt] using
      NativeCompactRequest.load_run source entry oracle state trace machine first second third
  rw [show 41 = 1 + 40 by decide, TimedExecution.eval_add, admission, PMF.pure_bind, executing_run, loaded, PMF.pure_map]

theorem original_body_shape {State : Type} (oracle : BitOracle State) (state : State)
    (machine : Machine.Configuration) (trace : List (List Bool × List Bool)) (message : Message)
    (table : PolygraphOracle.Table 8 0)
    (layout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (final : Configuration State)
    (supported : final ∈ (TimedExecution.eval (Reification.timedStep source oracle)
      (SimulatorLookupDispatch.steps (Backend.key message) table)
      (SimulatorQueryLoading.loadedFrame 8 0 state machine trace (Backend.request message))).support) :
    ∃ actual : Machine.Configuration, final = NativeCode.frame state trace actual ∧ actual.halted = true := by
  have full : SimulatorQueryLoading.Control.executing final ∈
      (TimedExecution.eval (SimulatorDispatchQueryLoading.step 8 0 oracle)
        (SimulatorDispatchQueryLoading.steps (Backend.key message) table)
        (.admitting state machine trace (Backend.request message))).support := by
    simp only [SimulatorDispatchQueryLoading.steps, SimulatorDispatchQueryLoading.step, Backend.request]
    rw [TimedExecution.eval_add,
      SimulatorQueryLoading.prepare_run, PMF.pure_bind, SimulatorQueryLoading.executing_run,
      PMF.mem_support_map_iff]
    exact ⟨final, supported, rfl⟩
  obtain ⟨_, _, actual, same, halted, _⟩ := SimulatorDispatchQueryLoading.native_layout oracle state machine trace
    (Backend.key message) table layout (by decide) _ full
  exact ⟨actual, SimulatorQueryLoading.Control.executing.inj same, halted⟩

theorem extended_body {State : Type} (oracle : BitOracle State) (state : State)
    (machine : Machine.Configuration) (trace : List (List Bool × List Bool)) (message : Message)
    (table : PolygraphOracle.Table 8 0)
    (layout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table))) :
    TimedExecution.eval (Reification.timedStep code oracle) (SimulatorLookupDispatch.steps (Backend.key message) table)
        (SimulatorQueryLoading.loadedFrame 8 0 state machine trace (Backend.request message)) =
      TimedExecution.eval (Reification.timedStep source oracle) (SimulatorLookupDispatch.steps (Backend.key message) table)
        (SimulatorQueryLoading.loadedFrame 8 0 state machine trace (Backend.request message)) := by
  apply CodePrefixExecution.append_running_final source (NativeCompactRequest.adapter entry) oracle
  intro final supported
  obtain ⟨actual, same, _⟩ := original_body_shape oracle state machine trace message table layout final supported
  rw [same]
  rfl

def steps (message : Message) (table : PolygraphOracle.Table 8 0) : Nat :=
  41 + SimulatorLookupDispatch.steps (Backend.key message) table

theorem steps_overhead (message : Message) (table : PolygraphOracle.Table 8 0) :
    steps message table = SimulatorDispatchQueryLoading.steps (Backend.key message) table + 8 := by
  simp only [steps, SimulatorDispatchQueryLoading.steps, SimulatorQueryLoading.prepareSteps,
    List.length_append, List.length_singleton, compressionPacket_length]
  omega

/-- Equality of full retained native frames, not just decoded responses.
The fixed program performs admission, real padding and the old cache branch. -/
theorem native_run {State : Type} (oracle : BitOracle State) (state : State)
    (machine : Machine.Configuration) (trace : List (List Bool × List Bool)) (message : Message)
    (table : PolygraphOracle.Table 8 0)
    (layout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table))) :
    TimedExecution.eval (step oracle) (steps message table) (.admitting state machine trace (encodeMessage message)) =
      TimedExecution.eval (SimulatorDispatchQueryLoading.step 8 0 oracle)
        (SimulatorDispatchQueryLoading.steps (Backend.key message) table)
        (.admitting state machine trace (Backend.request message)) := by
  rw [steps, TimedExecution.eval_add, prepare_run, PMF.pure_bind, executing_run, extended_body oracle state machine trace message table layout]
  symm
  simp only [SimulatorDispatchQueryLoading.steps, SimulatorDispatchQueryLoading.step, Backend.request]
  rw [TimedExecution.eval_add,
    SimulatorQueryLoading.prepare_run, PMF.pure_bind, SimulatorQueryLoading.executing_run]

theorem native_halts {State : Type} (oracle : BitOracle State) (state : State)
    (machine : Machine.Configuration) (trace : List (List Bool × List Bool)) (message : Message)
    (table : PolygraphOracle.Table 8 0)
    (layout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (final : SimulatorQueryLoading.Control State)
    (supported : final ∈ (TimedExecution.eval (step oracle) (steps message table)
      (.admitting state machine trace (encodeMessage message))).support) :
    ∃ actual : Machine.Configuration, final = .executing (NativeCode.frame state trace actual) ∧ actual.halted = true := by
  rw [native_run oracle state machine trace message table layout] at supported
  obtain ⟨_, _, actual, same, halted, _⟩ := SimulatorDispatchQueryLoading.native_layout oracle state machine trace
    (Backend.key message) table layout (by decide) final supported
  exact ⟨actual, same, halted⟩

theorem steps_budget (message : Message) (table : PolygraphOracle.Table 8 0) (entries : Nat)
    (size : table.length ≤ entries) : steps message table ≤ 146 * entries + 195 := by
  have old := SimulatorDispatchQueryLoading.steps_le (Backend.key message) table (by decide)
  rw [steps_overhead]
  dsimp at old
  omega

/-- Actual updated table and response cells on the retained machine. The
mathematical table is a proof parameter, never a runtime constructor. -/
theorem native_retained {State : Type} (oracle : BitOracle State) (state : State)
    (machine : Machine.Configuration) (trace : List (List Bool × List Bool)) (message : Message)
    (table : PolygraphOracle.Table 8 0)
    (layout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (final : SimulatorQueryLoading.Control State)
    (supported : final ∈ (TimedExecution.eval (step oracle) (steps message table)
      (.admitting state machine trace (encodeMessage message))).support) :
    ∃ (value : Bits 8) (before : List (Option Bool)) (actual : Machine.Configuration),
      final = .executing (NativeCode.frame state trace actual) ∧ actual.halted = true ∧
      actual.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits
        (if (table.lookup (Backend.key message)).isSome then table else (Backend.key message, value) :: table))) ∧
      before.getD 0 none = none ∧
      actual.outputTape.Equivalent (FixedWidthCopy.frontier before (value.toList.map some ++ [none])) ∧
      SimulatorDispatchQueryLoading.headBits actual.outputTape = value.toList := by
  rw [native_run oracle state machine trace message table layout] at supported
  exact SimulatorDispatchQueryLoading.native_layout oracle state machine trace (Backend.key message) table layout
    (by decide) final supported

end Foundation.Hash.Native.CompactMACQuery
