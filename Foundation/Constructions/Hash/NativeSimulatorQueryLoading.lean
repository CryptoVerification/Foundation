import Foundation.Constructions.Hash.NativeSimulatorLookupContextRestore
import Foundation.Crypto.Semantics.Oracle.NativeCodeTapeEquivalence
import Foundation.Crypto.Semantics.Machine.NativePacketService

/-! A charged controller admission and the existing cell-by-cell loader
place a raw next query on the retained physical machine. Only the PC and
halt flag change at admission; the table and both old tapes are retained
while the loader writes its separate working tape. No query decoding or
mathematical table construction is performed by the runtime controller. -/
namespace Foundation.Hash.Native.SimulatorQueryLoading
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev code := SimulatorLookupContextRestore.code

inductive Control (State : Type*) where
  | admitting (state : State) (machine : Machine.Configuration)
      (trace : List (List Bool × List Bool)) (request : List Bool)
  | executing (frame : Configuration State)

noncomputable def step {State : Type*} (program : Code) (n κ : Nat) (oracle : BitOracle State) : Control State → PMF (Control State)
  | .admitting state machine trace request =>
      PMF.pure (.executing ⟨state, .loading (machine.resumeAt (SimulatorLookup.headerPc n κ)) request {}, trace⟩)
  | .executing frame => (Reification.timedStep program oracle frame).map .executing

def boundary {State : Type*} : Control State → Bool
  | .admitting .. => false
  | .executing frame => Reification.terminal frame.control

def observe {State α : Type*} (read : Configuration State → α) : Control State → Option α
  | .admitting .. => none
  | .executing frame => some (read frame)

def loadingFrame {State : Type*} (n κ : Nat) (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (request : List Bool) : Configuration State :=
  ⟨state, .loading (machine.resumeAt (SimulatorLookup.headerPc n κ)) request {}, trace⟩

def loadedFrame {State : Type*} (n κ : Nat) (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (request : List Bool) : Configuration State :=
  NativeCode.frame state trace {machine.resumeAt (SimulatorLookup.headerPc n κ) with outputTape := ResponseLoading.loaded request}

def prepareSteps (request : List Bool) : Nat := 3 * request.length + 3

theorem executing_run {State : Type*} (program : Code) (n κ : Nat) (oracle : BitOracle State)
    (fuel : Nat) (frame : Configuration State) :
    TimedExecution.eval (step program n κ oracle) fuel (.executing frame) =
      (TimedExecution.eval (Reification.timedStep program oracle) fuel frame).map .executing := by
  induction fuel generalizing frame with
  | zero => simp [TimedExecution.eval, PMF.pure_map]
  | succ fuel ih => simp only [TimedExecution.eval, step, PMF.bind_map, PMF.map_bind, ih, Function.comp_def]

theorem prepare_run {State : Type*} (program : Code) (n κ : Nat) (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool)) (request : List Bool) :
    TimedExecution.eval (step program n κ oracle) (prepareSteps request) (.admitting state machine trace request) =
      PMF.pure (.executing (loadedFrame n κ state machine trace request)) := by
  have admission : TimedExecution.eval (step program n κ oracle) 1 (.admitting state machine trace request) =
      PMF.pure (.executing (loadingFrame n κ state machine trace request)) := by
    simp [TimedExecution.eval, step, loadingFrame]
  rw [show prepareSteps request = 1 + (3 * request.length + 2) by unfold prepareSteps; omega,
    TimedExecution.eval_add, admission, PMF.pure_bind, executing_run]
  unfold loadingFrame
  rw [ResponseLoading.run, PMF.pure_map]
  rfl

/-- Use the old loader's cell-equivalence proof; the represented final blank
is not removed. Every input cell, including saved cells, is retained exactly. -/
theorem loaded_entry {State : Type*} {n κ : Nat} (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeInput : List (Option Bool))
    (tableLayout : machine.inputTape.Equivalent {Tape.ofBits (SimulatorLookup.tableBits table) with left := beforeInput}) :
    NativeCode.CellEquivalent
      (loadedFrame n κ state machine trace (compressionPacket query ++ [false]))
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query (beforeInput) [])) := by
  apply NativeCode.CellEquivalent.running
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change machine.inputTape.Equivalent {Tape.ofBits (SimulatorLookup.tableBits table) with left := beforeInput}
    exact tableLayout
  · have h := (NativePacketService.loaded_equivalent (compressionPacket query ++ [false])).2.2.2
    cases raw : compressionPacket query ++ [false] <;>
      simpa [NativePacketService.loaded, Machine.Configuration.initial, Machine.Configuration.swapTapes,
        SimulatorLookup.scanStart, raw, Tape.ofBits] using h

/-- Entire physical loading, then the same finite native lookup/rewind code.
The observation must respect cells; it may include state, history and control.
It cannot replace a physical encoded-storage measurement by a shorter tape. -/
theorem query_run {State α : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (saved : List (Option Bool))
    (tableLayout : machine.inputTape.Equivalent {Tape.ofBits (SimulatorLookup.tableBits table) with left := none :: saved})
    (read : Configuration State → α)
    (respects : ∀ first second, NativeCode.CellEquivalent first second → read first = read second) :
    (TimedExecution.eval (step (code n κ) n κ oracle)
      (prepareSteps (compressionPacket query ++ [false]) + SimulatorLookupContextRestore.steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).map (observe read) =
      PMF.pure (some (read (SimulatorLookupContextRestore.finish state trace query table saved []))) := by
  rw [TimedExecution.eval_add, prepare_run, PMF.pure_bind, executing_run, PMF.map_comp]
  change (TimedExecution.eval _ _ (loadedFrame n κ state machine trace (compressionPacket query ++ [false]))).map
    (fun frame => some (read frame)) = _
  rw [NativeCode.eval_map_eq_of_cellEquivalent (code n κ) (SimulatorLookupRestore.code_native n κ)
    oracle _ _ _ (loaded_entry state machine trace query table (none :: saved) tableLayout)
    (fun frame => some (read frame)) (fun first second same => congrArg some (respects first second same)),
    SimulatorLookupContextRestore.run, PMF.pure_map]

/-- The actual run reaches a native halt; observing this flag does not alter
or normalize the retained frame. -/
theorem query_halts {State : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (saved : List (Option Bool))
    (tableLayout : machine.inputTape.Equivalent {Tape.ofBits (SimulatorLookup.tableBits table) with left := none :: saved})
    (target : Control State)
    (support : target ∈ (TimedExecution.eval (step (code n κ) n κ oracle)
      (prepareSteps (compressionPacket query ++ [false]) + SimulatorLookupContextRestore.steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).support) :
    boundary target = true := by
  have law := query_run oracle state machine trace query table saved tableLayout
    (fun frame => Reification.terminal frame.control) (fun _ _ same => same.terminal)
  have observed : observe (fun frame : Configuration State => Reification.terminal frame.control) target ∈
      ((TimedExecution.eval (step (code n κ) n κ oracle)
        (prepareSteps (compressionPacket query ++ [false]) + SimulatorLookupContextRestore.steps query table)
        (.admitting state machine trace (compressionPacket query ++ [false]))).map
        (observe (fun frame => Reification.terminal frame.control))).support :=
    by rw [PMF.mem_support_map_iff]; exact ⟨target, support, rfl⟩
  rw [law, PMF.mem_support_pure_iff] at observed
  cases target with
  | admitting => contradiction
  | executing frame => exact Option.some.inj observed

theorem boundary_absorbing {State : Type*} (program : Code) (n κ : Nat) (oracle : BitOracle State)
    (control : Control State) (stopped : boundary control = true) : step program n κ oracle control = PMF.pure control := by
  cases control with
  | admitting => contradiction
  | executing frame =>
      change Reification.terminal frame.control = true at stopped
      simp [step, Reification.timedStep, stopped, PMF.pure_map]

theorem prepare_first_joint {State : Type*} (program : Code) (n κ : Nat) (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool)) (request : List Bool) :
    runToBoundary (step program n κ oracle) boundary (prepareSteps request) (.admitting state machine trace request) =
      PMF.pure (.executing (loadedFrame n κ state machine trace request), prepareSteps request) := by
  have law := runToBoundary_joint_of_active_final (step program n κ oracle) boundary
    (boundary_absorbing program n κ oracle) (prepareSteps request) (.admitting state machine trace request)
    (by intro target support
        rw [prepare_run, PMF.mem_support_pure_iff] at support
        subst target
        rfl)
  rw [prepare_run, PMF.pure_map] at law
  exact law

theorem executing_first {State : Type*} (program : Code) (n κ : Nat) (oracle : BitOracle State)
    (fuel : Nat) (frame : Configuration State) :
    runToBoundary (step program n κ oracle) boundary fuel (.executing frame) =
      (runToBoundary (Reification.timedStep program oracle)
        (fun frame => Reification.terminal frame.control) fuel frame).map
        (fun result => (.executing result.1, result.2)) :=
  runToBoundary_map _ _ _ _ Control.executing (fun _ => rfl) (fun _ _ => rfl) fuel frame

/-- The actual first-halt clock includes admission, all request writes and
rewind steps, and the original sequential lookup and table restoration. -/
theorem query_first_joint {State α : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (saved : List (Option Bool))
    (tableLayout : machine.inputTape.Equivalent {Tape.ofBits (SimulatorLookup.tableBits table) with left := none :: saved})
    (read : Configuration State → α)
    (respects : ∀ first second, NativeCode.CellEquivalent first second → read first = read second) :
    (runToBoundary (step (code n κ) n κ oracle) boundary
      (prepareSteps (compressionPacket query ++ [false]) + SimulatorLookupContextRestore.steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).map
      (fun result => (observe read result.1, result.2)) =
      PMF.pure (some (read (SimulatorLookupContextRestore.finish state trace query table saved [])),
        prepareSteps (compressionPacket query ++ [false]) + SimulatorLookupContextRestore.steps query table) := by
  rw [runToBoundary_add, prepare_first_joint, PMF.pure_bind, executing_first, PMF.map_comp, PMF.map_comp]
  have same := NativeCode.first_bind_eq_of_cellEquivalent (code n κ) (SimulatorLookupRestore.code_native n κ)
    oracle (SimulatorLookupContextRestore.steps query table) _ _
    (loaded_entry state machine trace query table (none :: saved) tableLayout)
    (fun result => PMF.pure (some (read result.1), prepareSteps (compressionPacket query ++ [false]) + result.2))
    (fun first second time h => congrArg PMF.pure (congrArg
      (fun result => (some result, prepareSteps (compressionPacket query ++ [false]) + time)) (respects first second h)))
  rw [SimulatorLookupContextRestore.first_joint, PMF.pure_bind] at same
  exact same

/-- Every actual final frame retains the same state/history and physical
cells as the proved native endpoint. The actual represented lists survive. -/
theorem query_returned {State : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (saved : List (Option Bool))
    (tableLayout : machine.inputTape.Equivalent {Tape.ofBits (SimulatorLookup.tableBits table) with left := none :: saved})
    (target : Control State)
    (support : target ∈ (TimedExecution.eval (step (code n κ) n κ oracle)
      (prepareSteps (compressionPacket query ++ [false]) + SimulatorLookupContextRestore.steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).support) :
    ∃ actual, target = .executing actual ∧
      NativeCode.CellEquivalent actual (SimulatorLookupContextRestore.finish state trace query table saved []) := by
  let expected := SimulatorLookupContextRestore.finish state trace query table saved []
  have law := query_run oracle state machine trace query table saved tableLayout
    (fun actual => NativeCode.CellEquivalent actual expected)
    (fun first second same => propext ⟨fun h => same.symm.trans h, fun h => same.trans h⟩)
  have observed : observe (fun actual => NativeCode.CellEquivalent actual expected) target ∈
      ((TimedExecution.eval (step (code n κ) n κ oracle)
        (prepareSteps (compressionPacket query ++ [false]) + SimulatorLookupContextRestore.steps query table)
        (.admitting state machine trace (compressionPacket query ++ [false]))).map
        (observe (fun actual => NativeCode.CellEquivalent actual expected))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨target, support, rfl⟩
  rw [law, PMF.mem_support_pure_iff] at observed
  have reflexive : NativeCode.CellEquivalent expected expected :=
    .running state trace _ _ (Machine.Configuration.Equivalent.refl _)
  cases target with
  | admitting => contradiction
  | executing frame => exact ⟨frame, rfl, Eq.mpr (Option.some.inj observed) reflexive⟩

/-- The retained table is a valid cell-equivalent entry for the next query.
In particular no normalization, table reconstruction, or erasure of saved
cells is required between calls. Only a next raw request must be supplied. -/
theorem query_table_reusable {State : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (saved : List (Option Bool))
    (tableLayout : machine.inputTape.Equivalent {Tape.ofBits (SimulatorLookup.tableBits table) with left := none :: saved})
    (target : Control State)
    (support : target ∈ (TimedExecution.eval (step (code n κ) n κ oracle)
      (prepareSteps (compressionPacket query ++ [false]) + SimulatorLookupContextRestore.steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).support) :
    ∃ actual, target = .executing (NativeCode.frame state trace actual) ∧ actual.halted = true ∧
      actual.inputTape.Equivalent {Tape.ofBits (SimulatorLookup.tableBits table) with left := none :: saved} := by
  obtain ⟨frame, targetEq, same⟩ := query_returned oracle state machine trace query table saved tableLayout target support
  let expected := (NativeBitstringRewind.Scratch.finish
    (SimulatorLookupContextRestore.rewindInput query table saved [])).rebasePc (SimulatorLookup.lookupCode n κ).length
  change NativeCode.CellEquivalent frame (NativeCode.frame state trace expected) at same
  obtain ⟨actual, frameEq, cells⟩ := same.running_right state trace expected
  rw [frameEq] at targetEq
  have layout := SimulatorLookupContextRestore.finish_table state trace query table saved []
  change some expected.inputTape = some ({Tape.ofBits (SimulatorLookup.tableBits table) with left := none :: saved}) at layout
  refine ⟨actual, targetEq, cells.2.1.trans (show expected.halted = true by rfl), ?_⟩
  rw [← Option.some.inj layout]
  exact cells.2.2.1

theorem query_steps_le {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) :
    prepareSteps (compressionPacket query ++ [false]) + SimulatorLookupContextRestore.steps query table ≤
      table.length * (15 * n + 12 * κ + 26) + 15 * n + 10 * κ + 32 := by
  have bound := SimulatorLookupContextRestore.steps_le query table
  simp only [prepareSteps, List.length_append, List.length_singleton, compressionPacket_length]
  omega

end Foundation.Hash.Native.SimulatorQueryLoading
