import Foundation.Constructions.Hash.NativeSimulatorLookupRestoredHit
import Foundation.Constructions.Hash.NativeSimulatorFreshAfterLookupResponse

/-! One static code image chooses the cache-hit or missing continuation by
the actual exit reached by the original lookup. Neither the code nor its
transition function executes a host-side List.lookup. Terminal recognition
of previously absent queries remains a separate obligation. -/
namespace Foundation.Hash.Native.SimulatorLookupDispatch
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Cache continuation restores the table before positioning its response. -/
def hitBody (n : Nat) : Code :=
  CodeRelocation.host (NativeCode.subroutinePrefix rewindBitstring) (SimulatorLookupHitResponse.body n)

theorem hitBody_length (n : Nat) : (hitBody n).length = n + 9 := by
  simp [hitBody, CodeRelocation.code_length, NativeCode.subroutinePrefix_length,
    rewindBitstring, SimulatorLookupHitResponse.body_length]; omega

theorem hitBody_native (n : Nat) : ∀ op ∈ hitBody n, ∃ instruction, op = .native instruction := by
  apply CodeRelocation.host_native
  · intro op member
    simp only [NativeCode.subroutinePrefix, NativeCode.code, List.mem_map] at member
    obtain ⟨instruction, _, rfl⟩ := member
    exact ⟨_, rfl⟩
  · intro op member
    simp only [SimulatorLookupHitResponse.body, StraightLine.code, List.mem_append, List.mem_map,
      List.mem_singleton] at member
    rcases member with ⟨action, _, rfl⟩ | rfl <;> exact ⟨_, rfl⟩

def tail (n κ : Nat) : Code :=
  CodeRelocation.host (hitBody n) (SimulatorFreshAfterLookupResponse.code n κ)

def returnAt (n κ pc : Nat) : Nat :=
  if pc = SimulatorLookup.missingPc n κ + (n + κ + 1) + 2 then
    (SimulatorLookup.lookupCode n κ).length + (hitBody n).length
  else (SimulatorLookup.lookupCode n κ).length

def code (n κ : Nat) : Code :=
  HaltReturn.hostWithReturns (SimulatorLookup.lookupCode n κ) (tail n κ) (returnAt n κ)

theorem code_length (n κ : Nat) : (code n κ).length = 30 * n + 12 * κ + 112 := by
  simp [code, HaltReturn.hostWithReturns, CodeRelocation.code_length, tail,
    SimulatorLookup.lookupCode_length, hitBody_length,
    SimulatorFreshAfterLookupResponse.code_length]; omega

theorem code_native (n κ : Nat) : ∀ op ∈ code n κ, ∃ native, op = .native native := by
  apply CodeRelocation.host_native
  · exact HaltReturn.returnPrefix_native _ _ (SimulatorLookup.lookupCode_native n κ)
  · apply CodeRelocation.host_native
    · exact hitBody_native n
    · exact SimulatorFreshAfterLookupResponse.code_native n κ

theorem hit_return {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (SimulatorLookup.lookupSteps query table)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query beforeInput beforeOutput)) =
      PMF.pure (CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length
        (NativeCode.frame state trace ((SimulatorLookup.lookupFinish query table beforeInput beforeOutput).resumeAt 0))) := by
  have h := SimulatorLookup.lookup_return_targets (tail n κ) (returnAt n κ) oracle state trace query table beforeInput beforeOutput
  rw [SimulatorLookup.lookupFinish_pc, hit] at h
  have distinct : SimulatorLookup.copyPc n κ + 7 * n ≠ SimulatorLookup.missingPc n κ + (n + κ + 1) + 2 := by
    unfold SimulatorLookup.missingPc; omega
  simpa [code, returnAt, distinct, NativeCode.frame, CodeRelocation.frame, CodeRelocation.control,
    Configuration.resumeAt, Configuration.rebasePc] using h

theorem missing_return {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (SimulatorLookup.lookupSteps query table)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      PMF.pure (CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length
        (CodeRelocation.frame (hitBody n).length
          (NativeCode.frame state trace (SimulatorFreshAfterLookup.start query table beforeOutput)))) := by
  have h := SimulatorLookup.lookup_return_targets (tail n κ) (returnAt n κ) oracle state trace query table [] beforeOutput
  rw [SimulatorLookup.lookupFinish_pc, fresh] at h
  simpa [code, returnAt, SimulatorFreshAfterLookup.start, NativeCode.frame, CodeRelocation.frame,
    CodeRelocation.control, Configuration.resumeAt, Configuration.rebasePc] using h

/-- The same code image runs the cache continuation even though the missing
continuation is also present after it. Its final halt is retained. -/
theorem hit_stage_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (value : Bits n) (hit : table.lookup query = some value) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      (SimulatorLookup.lookupSteps query table + (SimulatorLookupRestore.rewindSteps query table + (n + 3 + halt.toNat)))
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      PMF.pure (SimulatorLookupRestoredHit.finish state trace query table beforeOutput value halt) := by
  rw [TimedExecution.eval_add, hit_return oracle state trace query table [] beforeOutput value hit, PMF.pure_bind]
  rw [SimulatorLookup.lookupRewind_entry]
  unfold code
  rw [HaltReturn.body_eval_with_targets]
  unfold tail hitBody
  rw [CodeRelocation.host_assoc, TimedExecution.eval_add, SimulatorLookupRestore.body_rewind_run, PMF.pure_bind]
  have placed := CodeRelocation.eval (NativeCode.subroutinePrefix rewindBitstring)
    (CodeRelocation.host (SimulatorLookupHitResponse.body n) (SimulatorFreshAfterLookupResponse.code n κ))
    oracle (n + 3 + halt.toNat)
    (NativeCode.frame state trace (SimulatorLookupRestore.afterRewind query table beforeOutput))
  change TimedExecution.eval _ (n + 3 + halt.toNat) (CodeRelocation.frame 5 _) = _ at placed
  rw [placed]
  have h := SimulatorLookupRestoredHit.body_stage_run_with_tail
    ((SimulatorFreshAfterLookupResponse.code n κ).map (CodeRelocation.instruction (SimulatorLookupHitResponse.body n).length))
    oracle state trace query table beforeOutput value hit halt
  change TimedExecution.eval (Reification.timedStep
    (CodeRelocation.host (SimulatorLookupHitResponse.body n) (SimulatorFreshAfterLookupResponse.code n κ)) oracle) _ _ = _ at h
  rw [h, PMF.pure_map, PMF.pure_map]
  rfl

theorem missing_stage_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) (positive : 0 < n) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      (SimulatorLookup.lookupSteps query table + (SimulatorFreshAfterLookup.rewindSteps table +
        (1 + (2 * n + (5 * n + 8 * (n + κ + 1) + 7 + halt.toNat)))))
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      (uniform (Bits n)).map (fun value => CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length
        (CodeRelocation.frame (hitBody n).length
          (SimulatorFreshAfterLookupResponse.finish state trace query table beforeOutput value halt))) := by
  rw [TimedExecution.eval_add, missing_return oracle state trace query table beforeOutput fresh, PMF.pure_bind]
  unfold code
  rw [HaltReturn.body_eval_with_targets]
  unfold tail
  rw [CodeRelocation.eval, SimulatorFreshAfterLookupResponse.stage_run oracle state trace query table beforeOutput fresh positive halt,
    PMF.map_comp, PMF.map_comp]
  rfl

/-- Proof-side duration of the branch reached by the physical lookup.
This expression is not an instruction and is not executed by the machine. -/
def steps {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) : Nat :=
  if (table.lookup query).isSome then SimulatorLookupRestoredHit.steps query table
  else SimulatorLookup.lookupSteps query table + SimulatorFreshAfterLookupResponse.steps table

/-- Full post-execution distribution of this cache-or-local-uniform
component. Absent recognized terminal queries require a further branch. -/
noncomputable def result {State : Type*} {n κ : Nat} (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (halt : Bool) : PMF (Configuration State) :=
  match table.lookup query with
  | some value => PMF.pure (SimulatorLookupRestoredHit.finish state trace query table beforeOutput value halt)
  | none => (uniform (Bits n)).map (fun value => CodeRelocation.frame (SimulatorLookup.lookupCode n κ).length
      (CodeRelocation.frame (hitBody n).length
        (SimulatorFreshAfterLookupResponse.finish state trace query table beforeOutput value halt)))

theorem stage_run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (positive : 0 < n) (halt : Bool) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps query table - 1 + halt.toNat)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      result state trace query table beforeOutput halt := by
  cases lookup : table.lookup query with
  | some value =>
      simp only [steps, result, lookup, Option.isSome_some, ↓reduceIte]
      have size : SimulatorLookupRestoredHit.steps query table - 1 + halt.toNat =
          SimulatorLookup.lookupSteps query table + (SimulatorLookupRestore.rewindSteps query table + (n + 3 + halt.toNat)) := by
        unfold SimulatorLookupRestoredHit.steps SimulatorLookupRestore.steps; omega
      rw [size]
      exact hit_stage_run oracle state trace query table beforeOutput value lookup halt
  | none =>
      simp only [steps, result, lookup, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      have size : SimulatorLookup.lookupSteps query table + SimulatorFreshAfterLookupResponse.steps table - 1 + halt.toNat =
          SimulatorLookup.lookupSteps query table + (SimulatorFreshAfterLookup.rewindSteps table +
            (1 + (2 * n + (5 * n + 8 * (n + κ + 1) + 7 + halt.toNat)))) := by
        unfold SimulatorFreshAfterLookupResponse.steps SimulatorFreshResponse.steps SimulatorRememberResponse.steps
        omega
      rw [size]
      exact missing_stage_run oracle state trace query table beforeOutput lookup positive halt

theorem result_terminal {State : Type*} {n κ : Nat}
    (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (halt : Bool) (frame : Configuration State)
    (support : frame ∈ (result state trace query table beforeOutput halt).support) :
    Reification.terminal frame.control = halt := by
  cases lookup : table.lookup query with
  | some value =>
      simp only [result, lookup, PMF.mem_support_pure_iff] at support
      subst frame
      rfl
  | none =>
      simp only [result, lookup, PMF.mem_support_map_iff] at support
      obtain ⟨value, _, rfl⟩ := support
      rfl

theorem steps_positive {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) :
    0 < steps query table := by
  unfold steps SimulatorLookupRestoredHit.steps SimulatorFreshAfterLookupResponse.steps
    SimulatorFreshResponse.steps SimulatorRememberResponse.steps
  split <;> omega

theorem run {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (positive : 0 < n) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps query table)
      (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      result state trace query table beforeOutput true := by
  have pos := steps_positive query table
  simpa only [Bool.toNat_true, show steps query table - 1 + 1 = steps query table by omega] using
    stage_run oracle state trace query table beforeOutput positive true

theorem first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (positive : 0 < n) :
    runToBoundary (Reification.timedStep (code n κ) oracle) (fun frame => Reification.terminal frame.control)
      (steps query table) (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) =
      (result state trace query table beforeOutput true).map (fun frame => (frame, steps query table)) := by
  have pos := steps_positive query table
  have adjacent : steps query table - 1 + 1 = steps query table := by omega
  have h := runToBoundary_joint_of_adjacent (Reification.timedStep (code n κ) oracle)
    (fun frame => Reification.terminal frame.control)
    (NativeCode.frame state trace (SimulatorLookup.scanStart table query [] beforeOutput)) (steps query table - 1)
    (by intro frame terminal; simp [Reification.timedStep, terminal])
    (by intro frame support
        have law := stage_run oracle state trace query table beforeOutput positive false
        simp only [Bool.toNat_false, Nat.add_zero] at law
        rw [law] at support
        exact result_terminal state trace query table beforeOutput false frame support)
    (by intro frame support
        rw [adjacent, run oracle state trace query table beforeOutput positive] at support
        exact result_terminal state trace query table beforeOutput true frame support)
  simpa only [adjacent, run oracle state trace query table beforeOutput positive] using h

/-- All native intermediate frames of the common code are counted,
including the original lookup and the statically selected continuation. -/
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

end Foundation.Hash.Native.SimulatorLookupDispatch
