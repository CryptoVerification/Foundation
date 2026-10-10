import Foundation.Constructions.Hash.NativeSimulatorFresh
import Foundation.Constructions.Hash.NativeSimulatorRewind
import Foundation.Crypto.Semantics.Oracle.StraightLine

/-! One actual finite continuation from a missing lookup: rewind the retained
table, move left over the response flag, generate fair bits, and prepend the
runtime key/value. Native halt in the rewind is compiled to a return jump.
This component requires positive tag width and a failed lookup; it does not
implement terminal recognition or the caller's original lookup invocation. -/
namespace Foundation.Hash.Native.SimulatorFreshAfterLookup
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def rewindPrefix : Code := NativeCode.subroutinePrefix rewindBitstring
private def moveFlag : Code := [.native (.moveLeft .output)]
def continuation (n κ : Nat) : Code := CodeRelocation.host moveFlag (SimulatorFresh.code n κ)
def code (n κ : Nat) : Code := CodeRelocation.host rewindPrefix (continuation n κ)

theorem rewindPrefix_length : rewindPrefix.length = 5 := by
  simp [rewindPrefix, NativeCode.subroutinePrefix_length, rewindBitstring]

theorem code_length (n κ : Nat) : (code n κ).length = 18 * n + 9 * κ + 22 := by
  simp [code, continuation, CodeRelocation.code_length, rewindPrefix_length,
    moveFlag, SimulatorFresh.code_length]; omega

def start {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) : Machine.Configuration :=
  (SimulatorLookup.lookupFinish query table [] beforeOutput).resumeAt 0

def finish {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (halt : Bool := true) : Configuration State :=
  CodeRelocation.frame 5 (CodeRelocation.frame 1
    (SimulatorFresh.finish state trace query table beforeOutput value halt))

def rewindSteps {n κ : Nat} (table : CompressionTable (Bits κ) (Bits n)) : Nat :=
  2 * (table.flatMap SimulatorLookup.entryBits).length + 4

def steps {n κ : Nat} (table : CompressionTable (Bits κ) (Bits n)) : Nat :=
  rewindSteps table + 1 + SimulatorFresh.steps n κ

def afterRewind {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) : Machine.Configuration :=
  (NativeBitstringRewind.finish (SimulatorLookup.rewindInput query table beforeOutput)).resumeAt 0

/-- Reuse the charged rewind and flag movement with any finite body. -/
def codeWithBody (body : Code) : Code :=
  CodeRelocation.host rewindPrefix (CodeRelocation.host moveFlag body)

theorem codeWithBody_length (body : Code) : (codeWithBody body).length = 6 + body.length := by
  simp [codeWithBody, CodeRelocation.code_length, rewindPrefix_length, moveFlag]; omega

theorem codeWithBody_native (body : Code)
    (native : ∀ instruction ∈ body, ∃ op, instruction = .native op) :
    ∀ instruction ∈ codeWithBody body, ∃ op, instruction = .native op := by
  apply CodeRelocation.host_native
  · intro instruction member
    simp only [rewindPrefix, NativeCode.subroutinePrefix, NativeCode.code, List.mem_map] at member
    obtain ⟨op, _, rfl⟩ := member
    exact ⟨_, rfl⟩
  · apply CodeRelocation.host_native
    · intro instruction member
      simp only [moveFlag, List.mem_cons, List.not_mem_nil, or_false] at member
      subst instruction
      exact ⟨_, rfl⟩
    · exact native

/-- Exact first return from the compiled rewind for an arbitrary body. -/
theorem withBody_rewind_first_return {State : Type*} {n κ : Nat}
    (body : Code) (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) :
    runToBoundary (Reification.timedStep (codeWithBody body) oracle)
      (NativeCode.returnBoundary 5) (rewindSteps table)
      (NativeCode.frame state trace (start query table beforeOutput)) =
      PMF.pure (CodeRelocation.frame 5 (NativeCode.frame state trace
        (afterRewind query table beforeOutput)), rewindSteps table) := by
  have h := SimulatorLookup.rewind_first_return
    ((CodeRelocation.host moveFlag body).map (CodeRelocation.instruction 5))
    oracle state trace query table beforeOutput fresh
  simp only [codeWithBody, CodeRelocation.host, rewindPrefix_length]
  simpa only [rewindPrefix, start, rewindSteps, afterRewind, CodeRelocation.host, CodeRelocation.frame,
    CodeRelocation.control, NativeCode.frame, Configuration.resumeAt, Configuration.rebasePc, Nat.add_zero] using h

/-- The prelude executes its rewind return jump and flag movement before
reaching the relocated body. All inherited physical tape cells are retained. -/
theorem prepare_run {State : Type*} {n κ : Nat}
    (body : Code) (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) :
    TimedExecution.eval (Reification.timedStep (codeWithBody body) oracle) (rewindSteps table + 1)
      (NativeCode.frame state trace (start query table beforeOutput)) =
      PMF.pure (CodeRelocation.frame 5 (CodeRelocation.frame 1
        (NativeCode.frame state trace (SimulatorFresh.startAtFlag query table beforeOutput)))) := by
  have rewind := withBody_rewind_first_return body oracle state trace query table beforeOutput fresh
  have move : TimedExecution.eval (Reification.timedStep (CodeRelocation.host moveFlag body) oracle) 1
      (NativeCode.frame state trace (afterRewind query table beforeOutput)) =
      PMF.pure (CodeRelocation.frame 1
        (NativeCode.frame state trace (SimulatorFresh.startAtFlag query table beforeOutput))) := by
    have layout := SimulatorLookup.rewind_table_layout query table beforeOutput
    simp only [afterRewind, Machine.Configuration.resumeAt]
    rw [layout]
    simp [TimedExecution.eval, CodeRelocation.host, moveFlag, Reification.timedStep,
      Reification.terminal, Reification.perform, Reification.action, transition,
      NativeCode.frame, NativeBitstringRewind.finish, SimulatorLookup.rewindInput,
      SimulatorLookup.missingFinish, SimulatorLookup.scanStart, SimulatorFresh.startAtFlag,
      SimulatorFresh.start, Machine.Instruction.next, Configuration.advance, Configuration.updateTape,
      Tape.moveLeft, CodeRelocation.frame, CodeRelocation.control, Configuration.rebasePc]
  rw [runToBoundary_law _ (NativeCode.returnBoundary 5) (rewindSteps table) _ _ (by omega),
    rewind, PMF.pure_bind, Nat.add_sub_cancel_left]
  have h := CodeRelocation.eval rewindPrefix (CodeRelocation.host moveFlag body) oracle 1
    (NativeCode.frame state trace (afterRewind query table beforeOutput))
  rw [move, PMF.pure_map] at h
  simpa only [codeWithBody, rewindPrefix_length] using h

/-- Whole execution of an arbitrary body from the prepared flag entry.
Relocation changes actual addresses; no intermediate resume is executed. -/
theorem withBody_run {State : Type*} {n κ : Nat}
    (body : Code) (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) (fuel : Nat) :
    TimedExecution.eval (Reification.timedStep (codeWithBody body) oracle) (rewindSteps table + 1 + fuel)
      (NativeCode.frame state trace (start query table beforeOutput)) =
      (TimedExecution.eval (Reification.timedStep body oracle) fuel
        (NativeCode.frame state trace (SimulatorFresh.startAtFlag query table beforeOutput))).map
          (fun frame => CodeRelocation.frame 5 (CodeRelocation.frame 1 frame)) := by
  rw [TimedExecution.eval_add, prepare_run body oracle state trace query table beforeOutput fresh, PMF.pure_bind]
  have outer := CodeRelocation.eval rewindPrefix (CodeRelocation.host moveFlag body) oracle fuel
    (CodeRelocation.frame 1 (NativeCode.frame state trace (SimulatorFresh.startAtFlag query table beforeOutput)))
  have inner := CodeRelocation.eval moveFlag body oracle fuel
    (NativeCode.frame state trace (SimulatorFresh.startAtFlag query table beforeOutput))
  simp only [show moveFlag.length = 1 from rfl] at inner
  rw [inner, PMF.map_comp] at outer
  simpa only [codeWithBody, rewindPrefix_length, Function.comp_def] using outer

/-- Exact first return from the existing charged rewind, in this same
whole continuation code and with the actual retained table/source cells. -/
theorem rewind_first_return {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) :
    runToBoundary (Reification.timedStep (code n κ) oracle)
      (NativeCode.returnBoundary 5) (rewindSteps table)
      (NativeCode.frame state trace (start query table beforeOutput)) =
      PMF.pure (CodeRelocation.frame 5
        (NativeCode.frame state trace (afterRewind query table beforeOutput)), rewindSteps table) := by
  have h := withBody_rewind_first_return (SimulatorFresh.code n κ)
    oracle state trace query table beforeOutput fresh
  simpa only [codeWithBody, code, continuation] using h

/-- Adjacent horizons of one full run. Intermediate rewind returns via an
executed jump; sampling and writing proceed on its inherited physical tapes. -/
theorem stage_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) (positive : 0 < n) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      (rewindSteps table + (1 + (2 * n + (5 * n + 7 * (n + κ + 1) + 5 + halt.toNat))))
      (NativeCode.frame state trace (start query table beforeOutput)) =
      (uniform (Bits n)).map (fun value => finish state trace query table beforeOutput value halt) := by
  have h := withBody_run (SimulatorFresh.code n κ) oracle state trace query table beforeOutput fresh
    (2 * n + (5 * n + 7 * (n + κ + 1) + 5 + halt.toNat))
  rw [SimulatorFresh.stage_run_at_flag oracle state trace query table beforeOutput positive halt, PMF.map_comp] at h
  simpa only [codeWithBody, code, continuation, finish, Function.comp_def, Nat.add_assoc] using h

theorem steps_eq {n κ : Nat} (table : CompressionTable (Bits κ) (Bits n)) :
    steps table = 2 * ((3 * n + 2 * κ + 4) * table.length) + 14 * n + 7 * κ + 18 := by
  have size := SimulatorLookup.tableBits_length table
  simp only [SimulatorLookup.tableBits, List.length_append, List.length_cons, List.length_nil] at size
  unfold steps rewindSteps SimulatorFresh.steps SimulatorRemember.steps
  omega

theorem code_native (n κ : Nat) :
    ∀ instruction ∈ code n κ, ∃ native, instruction = .native native := by
  have h := codeWithBody_native (SimulatorFresh.code n κ) (SimulatorFresh.code_native n κ)
  simpa only [codeWithBody, code, continuation] using h

theorem run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) (positive : 0 < n) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps table)
      (NativeCode.frame state trace (start query table beforeOutput)) =
      (uniform (Bits n)).map (fun value => finish state trace query table beforeOutput value) := by
  simpa [steps, SimulatorFresh.steps, SimulatorRemember.steps, Nat.add_assoc] using
    stage_run oracle state trace query table beforeOutput fresh positive true

theorem first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) (positive : 0 < n) :
    runToBoundary (Reification.timedStep (code n κ) oracle)
      (fun frame => Reification.terminal frame.control) (steps table)
      (NativeCode.frame state trace (start query table beforeOutput)) =
      (uniform (Bits n)).map (fun value => (finish state trace query table beforeOutput value, steps table)) := by
  have adjacent : steps table - 1 + 1 = steps table := by
    unfold steps SimulatorFresh.steps SimulatorRemember.steps; omega
  have h := runToBoundary_joint_of_adjacent (Reification.timedStep (code n κ) oracle)
    (fun frame => Reification.terminal frame.control)
    (NativeCode.frame state trace (start query table beforeOutput)) (steps table - 1)
    (by intro frame terminal; simp [Reification.timedStep, terminal])
    (by intro frame support
        have law := stage_run oracle state trace query table beforeOutput fresh positive false
        have size : steps table - 1 = rewindSteps table + (1 + (2 * n + (5 * n + 7 * (n + κ + 1) + 5))) := by
          unfold steps SimulatorFresh.steps SimulatorRemember.steps; omega
        simp only [Bool.toNat_false, Nat.add_zero] at law
        rw [size, law, PMF.mem_support_map_iff] at support
        obtain ⟨value, _, rfl⟩ := support
        rfl)
    (by intro frame support
        rw [adjacent, run oracle state trace query table beforeOutput fresh positive, PMF.mem_support_map_iff] at support
        obtain ⟨value, _, rfl⟩ := support
        rfl)
  simpa only [adjacent, run oracle state trace query table beforeOutput fresh positive,
    PMF.map_comp, Function.comp_def] using h

/-- All supported intermediate physical frames, including the rewind,
old flag, local randomness, table writes, full private state and history. -/
theorem encoded_peak {State : Type*} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool))
    (horizon elapsed : Nat) (within : elapsed ≤ horizon) (target : Configuration State)
    (support : target ∈ (TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      elapsed (NativeCode.frame state trace (start query table beforeOutput))).support) :
    ((NativeCode.fullEncoding E).encode (code n κ, target)).length ≤
      NativeCode.storageBound (code n κ)
        (NativePacketComponent.Resources.frameSize stateSize
          (NativeCode.frame state trace (start query table beforeOutput))) horizon := by
  exact NativeCode.encoded_peak E stateSize hState oracle state trace (code n κ) (code_native n κ)
    (start query table beforeOutput) horizon elapsed within target support

/-- Cache/state marginal of the fixed simulator from the actual missing
lookup's physical tapes. Terminal recognition is still an explicit condition. -/
theorem fresh_branch_table {State : Type} {n κ : Nat}
    (oracle : BitOracle State) (ideal : Oracle (List (Bits κ)) (Bits n) State)
    (initial : Bits n) (terminal : Bits κ) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) (positive : 0 < n)
    (unrecognized : terminalMessage initial terminal table query = none) :
    (TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps table)
      (NativeCode.frame state trace (start query table beforeOutput))).map SimulatorFresh.storedTable =
      (compressionSimulator ideal initial terminal (table, state) query).map
        (fun result => (result.1.2, trace, Tape.ofBits (SimulatorLookup.tableBits result.1.1))) := by
  rw [run oracle state trace query table beforeOutput fresh positive,
    compressionSimulator_terminal_eq, fresh, unrecognized, PMF.map_comp, PMF.map_comp]
  rfl

/-- The branch contract carries the actual failed lookup and positive
width requirements. It does not assume the final simulation conclusion. -/
structure Input (State : Type*) (n κ : Nat) where
  data : SimulatorFresh.Input State n κ
  fresh : data.table.lookup data.query = none
  positive : 0 < n

noncomputable def procedure {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure (Reification.timedStep (code n κ) oracle) (Input State n κ) (Configuration State) :=
  TimedExecution.Procedure.ofFixed _
    (fun input => NativeCode.frame input.data.state input.data.trace
      (start input.data.query input.data.table input.data.beforeOutput))
    (fun _ output => output)
    (fun input => (uniform (Bits n)).map (fun value => finish input.data.state input.data.trace
      input.data.query input.data.table input.data.beforeOutput value))
    (fun input => steps input.data.table)
    (fun input => by rw [run oracle _ _ _ _ _ input.fresh input.positive, PMF.map_comp]; rfl)

theorem procedure_operational {State : Type*} (n κ : Nat) (oracle : BitOracle State) :
    Procedure.Operational (procedure n κ oracle) := by
  apply Procedure.operational_ofFixed

theorem procedure_first_joint {State : Type*} (n κ : Nat) (oracle : BitOracle State)
    (input : Input State n κ) :
    runToBoundary (Reification.timedStep (code n κ) oracle)
      (fun frame => Reification.terminal frame.control)
      ((procedure n κ oracle).budget input) ((procedure n κ oracle).entry input) =
      (procedure n κ oracle).costed input := by
  change runToBoundary _ _ (steps input.data.table)
    (NativeCode.frame input.data.state input.data.trace
      (start input.data.query input.data.table input.data.beforeOutput)) = _
  rw [first_joint oracle _ _ _ _ _ input.fresh input.positive]
  simp only [procedure, TimedExecution.Procedure.ofFixed, PMF.map_comp, Function.comp_def]

theorem first_encoded {State : Type*} (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool))
    (result : Configuration State × Nat)
    (support : result ∈ (runToBoundary (Reification.timedStep (code n κ) oracle)
      (fun frame => Reification.terminal frame.control) (steps table)
      (NativeCode.frame state trace (start query table beforeOutput))).support) :
    ((NativeCode.fullEncoding E).encode (code n κ, result.1)).length ≤
      NativeCode.storageBound (code n κ)
        (NativePacketComponent.Resources.frameSize stateSize
          (NativeCode.frame state trace (start query table beforeOutput))) result.2 := by
  exact encoded_peak E stateSize hState oracle state trace query table beforeOutput
    result.2 result.2 (Nat.le_refl _) result.1 (runToBoundary_reachable _ _ _ _ result support)

end Foundation.Hash.Native.SimulatorFreshAfterLookup
