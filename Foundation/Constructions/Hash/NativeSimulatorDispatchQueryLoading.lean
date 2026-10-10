import Foundation.Crypto.Semantics.Machine.TapeReading
import Foundation.Constructions.Hash.NativeSimulatorQueryLoadingResources
import Foundation.Constructions.Hash.NativeSimulatorLookupDispatchPacket

/-! Physical request admission/loading followed by the existing unified
cache-or-local-uniform native code. Observations below read actual table and
response cells; packet export and terminal recognition are separate stages. -/
namespace Foundation.Hash.Native.SimulatorDispatchQueryLoading
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev code := SimulatorLookupDispatch.code
noncomputable abbrev step {State : Type*} (n κ : Nat) (oracle : BitOracle State) := SimulatorQueryLoading.step (code n κ) n κ oracle

def steps {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) : Nat :=
  SimulatorQueryLoading.prepareSteps (compressionPacket query ++ [false]) + SimulatorLookupDispatch.steps query table

/-- Read current/right written cells, excluding the retained old query on
the left. This is a mathematical observation, not an executed packet scan. -/
def headBits (tape : Tape) : List Bool := ({tape with left := []} : Tape).bits

theorem headBits_equivalent {first second : Tape} (same : first.Equivalent second) : headBits first = headBits second := by
  apply Tape.Equivalent.bits
  exact ⟨same.1, fun _ => rfl, same.2.2⟩

def view {State : Type*} (frame : Configuration State) : State × List (List Bool × List Bool) × Option (List Bool × List Bool) :=
  (frame.state, frame.reverseTrace, match frame.control with
    | .running machine => some (machine.inputTape.bits, headBits machine.outputTape)
    | _ => none)

theorem view_equivalent {State : Type*} (first second : Configuration State)
    (same : NativeCode.CellEquivalent first second) : view first = view second := by
  cases same with
  | running state trace first second same =>
      simp only [view, NativeCode.frame, same.2.2.1.bits, headBits_equivalent same.2.2.2]
  | finished => rfl

theorem native_run {State α : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (read : Configuration State → α)
    (respects : ∀ first second, NativeCode.CellEquivalent first second → read first = read second) :
    (TimedExecution.eval (step n κ oracle) (steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).map (SimulatorQueryLoading.observe read) =
      (SimulatorLookupDispatch.result state trace query table [] true).map (fun frame => some (read frame)) := by
  unfold steps step
  rw [TimedExecution.eval_add, SimulatorQueryLoading.prepare_run, PMF.pure_bind,
    SimulatorQueryLoading.executing_run, PMF.map_comp]
  change (TimedExecution.eval _ _ (SimulatorQueryLoading.loadedFrame n κ state machine trace
    (compressionPacket query ++ [false]))).map (fun frame => some (read frame)) = _
  have entry := SimulatorQueryLoading.loaded_entry state machine trace query table []
    (by cases bits : SimulatorLookup.tableBits table <;> simpa [bits, Tape.ofBits] using tableLayout)
  rw [NativeCode.eval_map_eq_of_cellEquivalent (code n κ) (SimulatorLookupDispatch.code_native n κ)
    oracle _ _ _ entry (fun frame => some (read frame))
    (fun first second same => congrArg some (respects first second same)), SimulatorLookupDispatch.run]
  exact positive

theorem native_first_joint {State α : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (read : Configuration State → α)
    (respects : ∀ first second, NativeCode.CellEquivalent first second → read first = read second) :
    (runToBoundary (step n κ oracle) SimulatorQueryLoading.boundary (steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).map
      (fun result => (SimulatorQueryLoading.observe read result.1, result.2)) =
      (SimulatorLookupDispatch.result state trace query table [] true).map
        (fun frame => (some (read frame), steps query table)) := by
  unfold steps step
  rw [runToBoundary_add, SimulatorQueryLoading.prepare_first_joint, PMF.pure_bind,
    SimulatorQueryLoading.executing_first, PMF.map_comp, PMF.map_comp]
  have entry := SimulatorQueryLoading.loaded_entry state machine trace query table []
    (by cases bits : SimulatorLookup.tableBits table <;> simpa [bits, Tape.ofBits] using tableLayout)
  have same := NativeCode.first_bind_eq_of_cellEquivalent (code n κ) (SimulatorLookupDispatch.code_native n κ)
    oracle (SimulatorLookupDispatch.steps query table) _ _ entry
    (fun result => PMF.pure (some (read result.1), SimulatorQueryLoading.prepareSteps (compressionPacket query ++ [false]) + result.2))
    (fun first second time h => congrArg PMF.pure (congrArg
      (fun result => (some result, SimulatorQueryLoading.prepareSteps (compressionPacket query ++ [false]) + time))
      (respects first second h)))
  rw [SimulatorLookupDispatch.first_joint oracle state trace query table [] positive, PMF.bind_map] at same
  exact same

theorem result_reflexive {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (expected : Configuration State) (support : expected ∈ (SimulatorLookupDispatch.result state trace query table [] true).support) :
    NativeCode.CellEquivalent expected expected := by
  cases lookup : table.lookup query with
  | some value =>
      simp only [SimulatorLookupDispatch.result, lookup, PMF.mem_support_pure_iff] at support
      subst expected
      exact .running state trace _ _ (Machine.Configuration.Equivalent.refl _)
  | none =>
      simp only [SimulatorLookupDispatch.result, lookup, PMF.mem_support_map_iff] at support
      obtain ⟨value, _, rfl⟩ := support
      exact .running state trace _ _ (Machine.Configuration.Equivalent.refl _)

/-- Every actual end frame is related to a supported canonical end frame.
The statement retains the actual physical tapes instead of replacing them. -/
theorem native_returned {State : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (target : SimulatorQueryLoading.Control State)
    (support : target ∈ (TimedExecution.eval (step n κ oracle) (steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).support) :
    ∃ actual expected, target = .executing actual ∧
      expected ∈ (SimulatorLookupDispatch.result state trace query table [] true).support ∧
      NativeCode.CellEquivalent actual expected := by
  let read := fun frame : Configuration State => fun other => NativeCode.CellEquivalent frame other
  have law := native_run oracle state machine trace query table tableLayout positive read
    (fun first second same => funext fun other => propext ⟨fun h => same.symm.trans h, fun h => same.trans h⟩)
  have observed : SimulatorQueryLoading.observe read target ∈
      ((TimedExecution.eval (step n κ oracle) (steps query table)
        (.admitting state machine trace (compressionPacket query ++ [false]))).map
        (SimulatorQueryLoading.observe read)).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨target, support, rfl⟩
  rw [law, PMF.mem_support_map_iff] at observed
  obtain ⟨expected, supported, equal⟩ := observed
  cases target with
  | admitting => contradiction
  | executing actual =>
      refine ⟨actual, expected, rfl, supported, ?_⟩
      have h := congrFun (Option.some.inj equal) expected
      exact Eq.mp h (result_reflexive state trace query table expected supported)

theorem headBits_frontier (before : List (Option Bool)) (packet : List Bool) :
    headBits (FixedWidthCopy.frontier before (packet.map some ++ [none])) = packet := by
  cases packet <;> simp [headBits, FixedWidthCopy.frontier, ResponseLoading.fromCells, Tape.bits]

theorem restored_bits (bits : List Bool) : ({Tape.ofBits bits with left := [none]} : Tape).bits = bits := by
  cases bits <;> simp [Tape.ofBits, Tape.bits]

/-- The table and response observation use the same sampled value. -/
theorem result_view {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) :
    (SimulatorLookupDispatch.result state trace query table [] true).map view =
      (match table.lookup query with
      | some value => PMF.pure (state, trace, some (SimulatorLookup.tableBits table, value.toList))
      | none => (uniform (Bits n)).map fun value =>
          (state, trace, some (SimulatorLookup.tableBits ((query, value) :: table), value.toList))) := by
  cases lookup : table.lookup query with
  | some value =>
      simp only [SimulatorLookupDispatch.result, lookup, PMF.pure_map]
      have layout := SimulatorLookupRestoredHit.finish_table state trace query table [] value true
      change some ((SimulatorLookupRestoredHit.bodyFinish query table [] value true).rebasePc 5).inputTape = _ at layout
      simp only [view, SimulatorLookupRestoredHit.finish, CodeRelocation.frame, CodeRelocation.control,
        NativeCode.frame, Machine.Configuration.rebasePc]
      have input := Option.some.inj layout
      simp only [Machine.Configuration.rebasePc] at input
      rw [input]
      simp only [restored_bits, SimulatorLookupRestoredHit.bodyFinish, headBits_frontier]
  | none =>
      simp only [SimulatorLookupDispatch.result, lookup, PMF.map_comp]
      congr 1
      funext value
      simp [view, CodeRelocation.frame, CodeRelocation.control, NativeCode.frame,
        SimulatorFreshAfterLookupResponse.finish, SimulatorFreshResponse.finish,
        SimulatorRememberResponse.finish, Machine.Configuration.rebasePc,
        Tape.bits_ofBits, headBits_frontier]

theorem blank_head_equivalent (bits : List Bool) :
    ({Tape.ofBits bits with left := [none]} : Tape).Equivalent (Tape.ofBits bits) := by
  cases bits <;> refine ⟨rfl, ?_, fun _ => rfl⟩
  all_goals intro index; cases index <;> rfl

/-- Both canonical branches retain a complete table at its head and a
response packet preceded by a physically blank separator. -/
theorem result_layout {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (expected : Configuration State) (support : expected ∈ (SimulatorLookupDispatch.result state trace query table [] true).support) :
    ∃ (value : Bits n) (before : List (Option Bool)) (machine : Machine.Configuration),
      expected = NativeCode.frame state trace machine ∧ machine.halted = true ∧
      machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits
        (if (table.lookup query).isSome then table else (query, value) :: table))) ∧
      before.getD 0 none = none ∧
      machine.outputTape = FixedWidthCopy.frontier before (value.toList.map some ++ [none]) := by
  cases lookup : table.lookup query with
  | some value =>
      simp only [SimulatorLookupDispatch.result, lookup, PMF.mem_support_pure_iff] at support
      subst expected
      refine ⟨value, none :: (compressionPacket query).reverse.map some, _, rfl, rfl, ?_, rfl, ?_⟩
      · have layout := SimulatorLookupRestoredHit.finish_table state trace query table [] value true
        simp only [Option.isSome_some, ↓reduceIte]
        change some _ = some _ at layout
        have h := Option.some.inj layout
        rw [h]
        exact blank_head_equivalent _
      · simp [SimulatorLookupRestoredHit.bodyFinish, Machine.Configuration.rebasePc]
  | none =>
      simp only [SimulatorLookupDispatch.result, lookup, PMF.mem_support_map_iff] at support
      obtain ⟨value, _, rfl⟩ := support
      refine ⟨value, none :: (compressionPacket query).dropLast.reverse.map some ++ NativePacketSuffix.restoredBefore [],
        _, rfl, rfl, ?_, ?_, rfl⟩
      · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        exact Tape.Equivalent.refl _
      · simp

/-- Actual retained state is ready for a later request and for cell-by-cell
response export. The same value describes the new table and response cells. -/
theorem native_layout {State : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (target : SimulatorQueryLoading.Control State)
    (support : target ∈ (TimedExecution.eval (step n κ oracle) (steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).support) :
    ∃ (value : Bits n) (before : List (Option Bool)) (actual : Machine.Configuration),
      target = .executing (NativeCode.frame state trace actual) ∧ actual.halted = true ∧
      actual.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits
        (if (table.lookup query).isSome then table else (query, value) :: table))) ∧
      before.getD 0 none = none ∧
      actual.outputTape.Equivalent (FixedWidthCopy.frontier before (value.toList.map some ++ [none])) ∧
      headBits actual.outputTape = value.toList := by
  obtain ⟨frame, expected, targetEq, supported, same⟩ :=
    native_returned oracle state machine trace query table tableLayout positive target support
  obtain ⟨value, before, canonical, expectedEq, halted, input, blank, output⟩ :=
    result_layout state trace query table expected supported
  rw [expectedEq] at same
  obtain ⟨actual, frameEq, cells⟩ := same.running_right state trace canonical
  rw [frameEq] at targetEq
  refine ⟨value, before, actual, targetEq, cells.2.1.trans halted, cells.2.2.1.trans input, blank, ?_, ?_⟩
  · rw [← output]
    exact cells.2.2.2
  · rw [headBits_equivalent cells.2.2.2, output, headBits_frontier]

/-- Use the existing actual exporter on the retained native frame. This
lemma is an execution of every packet read and reversal, not a decoder. -/
theorem native_export {State : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (target : SimulatorQueryLoading.Control State)
    (support : target ∈ (TimedExecution.eval (step n κ oracle) (steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).support) :
    ∃ (value : Bits n) (actual : Machine.Configuration),
      target = .executing (NativeCode.frame state trace actual) ∧
      actual.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits
        (if (table.lookup query).isSome then table else (query, value) :: table))) ∧
      TimedExecution.eval (NativePacketComponent.step (code n κ) oracle) (2 * n + 5)
        (.computing (NativeCode.frame state trace actual)) =
        PMF.pure (.exporting (NativeCode.frame state trace actual) (.returned value.toList)) := by
  obtain ⟨value, before, actual, targetEq, halted, input, blank, output, _⟩ :=
    native_layout oracle state machine trace query table tableLayout positive target support
  refine ⟨value, actual, targetEq, input, ?_⟩
  simpa only [Bits.length_toList, NativeCode.frame] using NativePacketComponent.export_prefix_run (code n κ) oracle state actual trace
    value.toList before [] blank halted output

theorem response_correct_with_table {State : Type} {n κ : Nat}
    (oracle : BitOracle State) (ideal : Oracle (List (Bits κ)) (Bits n) State)
    (initial : Bits n) (terminal : Bits κ) (state : State) (machine : Machine.Configuration)
    (trace : List (List Bool × List Bool)) (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n)
    (admissible : table.lookup query = none → terminalMessage initial terminal table query = none) :
    (TimedExecution.eval (step n κ oracle) (steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).map (SimulatorQueryLoading.observe view) =
      (compressionSimulator ideal initial terminal (table, state) query).map
        (fun output => some (output.1.2, trace, some (SimulatorLookup.tableBits output.1.1, output.2.toList))) := by
  rw [native_run oracle state machine trace query table tableLayout positive view view_equivalent]
  rw [show (fun frame : Configuration State => some (view frame)) = some ∘ view by rfl,
    ← PMF.map_comp, result_view]
  cases lookup : table.lookup query <;>
    simp [compressionSimulator_terminal_eq, lookup, admissible, PMF.pure_map, PMF.map_comp, Function.comp_def]

theorem native_first_time {State : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) (result : SimulatorQueryLoading.Control State × Nat)
    (support : result ∈ (runToBoundary (step n κ oracle) SimulatorQueryLoading.boundary
      (steps query table) (.admitting state machine trace (compressionPacket query ++ [false]))).support) :
    result.2 = steps query table := by
  have law := native_first_joint oracle state machine trace query table tableLayout positive
    (fun _ => ()) (fun _ _ _ => rfl)
  have observed : (SimulatorQueryLoading.observe (fun _ => ()) result.1, result.2) ∈
      ((runToBoundary (step n κ oracle) SimulatorQueryLoading.boundary (steps query table)
        (.admitting state machine trace (compressionPacket query ++ [false]))).map
        (fun result => (SimulatorQueryLoading.observe (fun _ => ()) result.1, result.2))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨result, support, rfl⟩
  rw [law, PMF.mem_support_map_iff] at observed
  obtain ⟨_, _, equal⟩ := observed
  exact (congrArg Prod.snd equal).symm

/-- The full physical frame, rather than just a cell-invariant observation,
is retained in the actual first-halt distribution. -/
theorem native_first_full {State : Type*} {n κ : Nat} (oracle : BitOracle State)
    (state : State) (machine : Machine.Configuration) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (tableLayout : machine.inputTape.Equivalent (Tape.ofBits (SimulatorLookup.tableBits table)))
    (positive : 0 < n) :
    runToBoundary (step n κ oracle) SimulatorQueryLoading.boundary (steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false])) =
      (TimedExecution.eval (step n κ oracle) (steps query table)
        (.admitting state machine trace (compressionPacket query ++ [false]))).map
        (fun target => (target, steps query table)) := by
  have complete : ∀ target ∈ (TimedExecution.eval (step n κ oracle) (steps query table)
      (.admitting state machine trace (compressionPacket query ++ [false]))).support,
      SimulatorQueryLoading.boundary target = true := by
    intro target support
    obtain ⟨_, _, actual, rfl, halted, _⟩ :=
      native_layout oracle state machine trace query table tableLayout positive target support
    exact halted
  have marginal := (Block.stopped (step n κ oracle) SimulatorQueryLoading.boundary (steps query table)
    (.admitting state machine trace (compressionPacket query ++ [false]))).final_law
    (fun result support => SimulatorQueryLoading.boundary_absorbing (code n κ) n κ oracle result.1
      (runToBoundary_completes _ _ _ _ complete result support)) (steps query table) (Nat.le_refl _)
  rw [marginal, PMF.map_comp]
  conv_lhs => rw [← PMF.bind_pure (runToBoundary (step n κ oracle) SimulatorQueryLoading.boundary
    (steps query table) (.admitting state machine trace (compressionPacket query ++ [false])))]
  rw [PMF.map, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext result support
  change PMF.pure result = PMF.pure (result.1, steps query table)
  rw [← native_first_time oracle state machine trace query table tableLayout positive result support]

theorem steps_le {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (positive : 0 < n) :
    steps query table ≤ table.length * (15 * n + 12 * κ + 26) + 19 * n + 12 * κ + 35 := by
  have bound := SimulatorLookupDispatch.packetSteps_le query table positive
  simp only [SimulatorLookupDispatch.packetSteps] at bound
  simp only [steps, SimulatorQueryLoading.prepareSteps, List.length_append,
    List.length_singleton, compressionPacket_length]
  omega

end Foundation.Hash.Native.SimulatorDispatchQueryLoading
