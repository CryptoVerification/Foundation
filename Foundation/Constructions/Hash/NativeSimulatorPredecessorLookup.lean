import Foundation.Constructions.Hash.NativeSimulatorPredecessorStep
import Foundation.Constructions.Hash.MessagePrefixLoop
import Foundation.Crypto.Semantics.Oracle.SelectiveHaltReturn
import Foundation.Crypto.Semantics.Oracle.NativeCodeResources

/-! Ordered predecessor search on the original physical compression table.
Only the two next-record halt sites are replaced by restart jumps. The same
finite code is used for every finite table and runtime target; no table-length
dependent code is generated. -/
namespace Foundation.Hash.Native.SimulatorPredecessorLookup
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n κ : Nat}

def returns (n κ pc : Nat) : Bool :=
  (pc == SimulatorPredecessorStep.dataNextPc n κ) ||
    (pc == SimulatorPredecessorStep.terminalNextPc n κ)

def code (n κ : Nat) : Code :=
  SelectiveHaltReturn.code (SimulatorPredecessorStep.code n κ) 0 (returns n κ)

theorem code_length (n κ : Nat) : (code n κ).length = 5 * n + 4 * κ + 29 := by
  rw [code, SelectiveHaltReturn.code_length, SimulatorPredecessorStep.code_length]

theorem code_native (n κ : Nat) : ∀ op ∈ code n κ, ∃ native, op = .native native :=
  SelectiveHaltReturn.code_native _ _ _ (SimulatorPredecessorStep.code_native n κ)

theorem returns_data (n κ : Nat) : returns n κ (SimulatorPredecessorStep.dataNextPc n κ) = true := by
  simp [returns]

theorem returns_terminal (n κ : Nat) : returns n κ (SimulatorPredecessorStep.terminalNextPc n κ) = true := by
  simp [returns]

theorem returns_found (n κ : Nat) : returns n κ (SimulatorPredecessorStep.foundPc n κ) = false := by
  obtain ⟨hf, hd, ht, _⟩ := SimulatorPredecessorStep.pc_formulas n κ
  have hfd : SimulatorPredecessorStep.foundPc n κ ≠ SimulatorPredecessorStep.dataNextPc n κ := by omega
  have hft : SimulatorPredecessorStep.foundPc n κ ≠ SimulatorPredecessorStep.terminalNextPc n κ := by omega
  simp [returns, hfd, hft]

theorem returns_missing (n κ : Nat) : returns n κ (SimulatorPredecessorStep.missingPc n κ) = false := by
  obtain ⟨_, hd, ht, hm⟩ := SimulatorPredecessorStep.pc_formulas n κ
  have hmd : SimulatorPredecessorStep.missingPc n κ ≠ SimulatorPredecessorStep.dataNextPc n κ := by omega
  have hmt : SimulatorPredecessorStep.missingPc n κ ≠ SimulatorPredecessorStep.terminalNextPc n κ := by omega
  simp [returns, hmd, hmt]

theorem record_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      (SimulatorPredecessorStep.recordTime entry target + 1)
      (NativeCode.frame state trace (SimulatorPredecessorStep.entryStart entry target beforeInput beforeOutput inputTail outputTail)) =
      if entry.1.2.1 = false ∧ entry.2 = target then
        PMF.pure (NativeCode.frame state trace
          { SimulatorPredecessorStep.foundStart entry target beforeInput beforeOutput inputTail outputTail with
            pc := SimulatorPredecessorStep.foundPc n κ, halted := true })
      else PMF.pure (NativeCode.frame state trace
        (SimulatorPredecessorStep.nextStart entry target beforeInput beforeOutput inputTail outputTail)) := by
  have hp := SimulatorPredecessorStep.record_before_halt oracle state trace entry target
    beforeInput beforeOutput inputTail outputTail
  have ha := SimulatorPredecessorStep.recordBefore_active entry target beforeInput beforeOutput inputTail outputTail
  have hh := SimulatorPredecessorStep.recordBefore_halt entry target beforeInput beforeOutput inputTail outputTail
  cases hm : entry.1.2.1 with
  | true =>
      have hr : returns n κ (SimulatorPredecessorStep.recordBefore entry target beforeInput beforeOutput inputTail outputTail).pc = true := by
        simp only [SimulatorPredecessorStep.recordBefore, hm, ↓reduceIte]
        exact returns_terminal n κ
      have hrun := SelectiveHaltReturn.return_run (SimulatorPredecessorStep.code n κ) 0 (returns n κ)
        oracle state trace (SimulatorPredecessorStep.entryStart entry target beforeInput beforeOutput inputTail outputTail)
        (SimulatorPredecessorStep.recordBefore entry target beforeInput beforeOutput inputTail outputTail)
        (SimulatorPredecessorStep.recordTime entry target) ha hp hh hr
      simpa only [code, SimulatorPredecessorStep.recordBefore, hm, Bool.true_eq_false,
        false_and, ↓reduceIte, Machine.Configuration.resumeAt, SimulatorPredecessorStep.nextStart]
        using hrun
  | false =>
      by_cases he : entry.2 = target
      · have hr : returns n κ (SimulatorPredecessorStep.recordBefore entry target beforeInput beforeOutput inputTail outputTail).pc = false := by
          simp only [SimulatorPredecessorStep.recordBefore, hm, Bool.false_eq_true, ↓reduceIte, he]
          exact returns_found n κ
        have hrun := SelectiveHaltReturn.halt_run (SimulatorPredecessorStep.code n κ) 0 (returns n κ)
          oracle state trace (SimulatorPredecessorStep.entryStart entry target beforeInput beforeOutput inputTail outputTail)
          (SimulatorPredecessorStep.recordBefore entry target beforeInput beforeOutput inputTail outputTail)
          (SimulatorPredecessorStep.recordTime entry target) ha hp hh hr
        simpa only [code, SimulatorPredecessorStep.recordBefore, hm, Bool.false_eq_true,
          ↓reduceIte, he, and_self] using hrun
      · have hr : returns n κ (SimulatorPredecessorStep.recordBefore entry target beforeInput beforeOutput inputTail outputTail).pc = true := by
          simp only [SimulatorPredecessorStep.recordBefore, hm, Bool.false_eq_true, ↓reduceIte, he]
          exact returns_data n κ
        have hrun := SelectiveHaltReturn.return_run (SimulatorPredecessorStep.code n κ) 0 (returns n κ)
          oracle state trace (SimulatorPredecessorStep.entryStart entry target beforeInput beforeOutput inputTail outputTail)
          (SimulatorPredecessorStep.recordBefore entry target beforeInput beforeOutput inputTail outputTail)
          (SimulatorPredecessorStep.recordTime entry target) ha hp hh hr
        simpa only [code, SimulatorPredecessorStep.recordBefore, hm, Bool.false_eq_true,
          ↓reduceIte, he, and_false, Machine.Configuration.resumeAt, SimulatorPredecessorStep.nextStart]
          using hrun

theorem empty_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (target : Bits n)
    (beforeInput beforeOutput outputTail : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (n + 3)
      (NativeCode.frame state trace (SimulatorPredecessorStep.emptyStart target beforeInput beforeOutput outputTail)) =
      PMF.pure (NativeCode.frame state trace
        { SimulatorPredecessorStep.missingState target beforeInput beforeOutput outputTail with
          pc := SimulatorPredecessorStep.missingPc n κ, halted := true }) := by
  have hp := SimulatorPredecessorStep.empty_before_halt (κ := κ) oracle state trace target beforeInput beforeOutput outputTail
  have hrun := SelectiveHaltReturn.halt_run (SimulatorPredecessorStep.code n κ) 0 (returns n κ)
    oracle state trace (SimulatorPredecessorStep.emptyStart target beforeInput beforeOutput outputTail)
    { SimulatorPredecessorStep.missingState target beforeInput beforeOutput outputTail with pc := SimulatorPredecessorStep.missingPc n κ }
    (1 + (n + 1)) rfl hp (SimulatorPredecessorStep.missing_halt n κ) (returns_missing n κ)
  have htime : 1 + (n + 1) + 1 = n + 3 := by omega
  simpa only [code, htime] using hrun

def start (table : CompressionTable (Bits κ) (Bits n)) (target : Bits n)
    (beforeInput beforeOutput outputTail : List (Option Bool)) : Machine.Configuration :=
  { inputTape := FixedWidthCopy.frontier beforeInput ((SimulatorLookup.tableBits table).map some),
    outputTape := SimulatorPredecessorStep.queryTape target beforeOutput outputTail }

def steps (target : Bits n) : CompressionTable (Bits κ) (Bits n) → Nat
  | [] => n + 3
  | entry :: rest =>
      SimulatorPredecessorStep.recordTime entry target + 1 +
        if entry.1.2.1 = false ∧ entry.2 = target then 0 else steps target rest

def finish (target : Bits n) (beforeInput beforeOutput outputTail : List (Option Bool)) :
    CompressionTable (Bits κ) (Bits n) → Machine.Configuration
  | [] => { SimulatorPredecessorStep.missingState target beforeInput beforeOutput outputTail with
      pc := SimulatorPredecessorStep.missingPc n κ, halted := true }
  | entry :: rest =>
      if entry.1.2.1 = false ∧ entry.2 = target then
        { SimulatorPredecessorStep.foundStart entry target beforeInput beforeOutput
            ((SimulatorLookup.tableBits rest).map some) outputTail with
          pc := SimulatorPredecessorStep.foundPc n κ, halted := true }
      else finish target ((SimulatorLookup.entryBits entry).reverse.map some ++ beforeInput) beforeOutput outputTail rest

/-- Exact complete table search, including the entire physical table/query layout. -/
theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (target : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeInput beforeOutput outputTail : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps target table)
      (NativeCode.frame state trace (start table target beforeInput beforeOutput outputTail)) =
      PMF.pure (NativeCode.frame state trace (finish (κ := κ) target beforeInput beforeOutput outputTail table)) := by
  induction table generalizing beforeInput with
  | nil => exact empty_run oracle state trace target beforeInput beforeOutput outputTail
  | cons entry rest ih =>
      have hstart : start (entry :: rest) target beforeInput beforeOutput outputTail =
          SimulatorPredecessorStep.entryStart entry target beforeInput beforeOutput
            ((SimulatorLookup.tableBits rest).map some) outputTail := by
        simp only [start, SimulatorPredecessorStep.entryStart, SimulatorLookup.tableBits_cons, List.map_append]
      have hnext : SimulatorPredecessorStep.nextStart entry target beforeInput beforeOutput
          ((SimulatorLookup.tableBits rest).map some) outputTail =
          start rest target ((SimulatorLookup.entryBits entry).reverse.map some ++ beforeInput) beforeOutput outputTail := rfl
      by_cases hm : entry.1.2.1 = false ∧ entry.2 = target
      · rw [steps, if_pos hm, Nat.add_zero, hstart,
          record_run oracle state trace entry target beforeInput beforeOutput
            ((SimulatorLookup.tableBits rest).map some) outputTail, if_pos hm, finish, if_pos hm]
      · rw [steps, if_neg hm, hstart, TimedExecution.eval_add,
          record_run oracle state trace entry target beforeInput beforeOutput
            ((SimulatorLookup.tableBits rest).map some) outputTail, if_neg hm,
          PMF.pure_bind, hnext, ih, finish, if_neg hm]

theorem steps_bound (target : Bits n) (table : CompressionTable (Bits κ) (Bits n)) :
    steps target table ≤ table.length * (8 * n + 2 * κ + 14) + n + 3 := by
  induction table with
  | nil => simp [steps]
  | cons entry rest ih =>
      have hb := SimulatorPredecessorStep.recordTime_bound entry target
      simp only [steps, List.length_cons, Nat.add_mul, Nat.one_mul]
      split <;> omega

/-- The native result flag agrees with ordered predecessor selection, including
output collisions and terminal entries having the same response as the target. -/
theorem finish_status (target : Bits n) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput outputTail : List (Option Bool)) :
    (finish target beforeInput beforeOutput outputTail table).outputTape.current =
      some (MessagePrefixLoop.find target table).1.isSome := by
  induction table generalizing beforeInput with
  | nil => rfl
  | cons entry rest ih =>
      by_cases hm : entry.1.2.1 = false ∧ entry.2 = target
      · simp only [finish, MessagePrefixLoop.find, hm]
        rfl
      · simp only [finish, MessagePrefixLoop.find, hm, ↓reduceIte]
        exact ih _

theorem finish_status_lookup (target : Bits n) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput outputTail : List (Option Bool)) :
    (finish target beforeInput beforeOutput outputTail table).outputTape.current =
      some ((dataEdges table).lookup target).isSome := by
  rw [finish_status, MessagePrefixLoop.find_eq]

theorem finish_halted (target : Bits n) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput outputTail : List (Option Bool)) :
    (finish target beforeInput beforeOutput outputTail table).halted = true := by
  induction table generalizing beforeInput with
  | nil => rfl
  | cons entry rest ih =>
      simp only [finish]
      split
      · rfl
      · exact ih _

/-- The selected predecessor is the first matching data record in the original
table, and its encoded key remains immediately before the returned table cursor. -/
theorem selected_layout (target previous : Bits n) (block : Bits κ)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeInput beforeOutput outputTail : List (Option Bool))
    (hfind : (MessagePrefixLoop.find target table).1 = some (previous, block)) :
    ∃ before after,
      table = before ++ ((previous, (false, block)), target) :: after ∧
      (∀ entry ∈ before, ¬ (entry.1.2.1 = false ∧ entry.2 = target)) ∧
      (finish target beforeInput beforeOutput outputTail table).inputTape =
        FixedWidthCopy.frontier
          ((SimulatorLookup.entryBits ((previous, (false, block)), target)).reverse.map some ++
            (before.flatMap SimulatorLookup.entryBits).reverse.map some ++ beforeInput)
          ((SimulatorLookup.tableBits after).map some) := by
  induction table generalizing beforeInput with
  | nil => simp [MessagePrefixLoop.find] at hfind
  | cons entry rest ih =>
      by_cases hm : entry.1.2.1 = false ∧ entry.2 = target
      · have hp : some (entry.1.1, entry.1.2.2) = some (previous, block) := by
          simpa [MessagePrefixLoop.find, hm] using hfind
        have he : entry = ((previous, (false, block)), target) := by
          have hpair := Option.some.inj hp
          rcases entry with ⟨⟨p, marker, b⟩, out⟩
          simp only [Prod.mk.injEq] at hpair
          simp only at hm
          rcases hm with ⟨rfl, rfl⟩
          rcases hpair with ⟨rfl, rfl⟩
          rfl
        refine ⟨[], rest, by simp [he], by intro e hin; simp at hin, ?_⟩
        simp only [finish, SimulatorPredecessorStep.foundStart,
          SimulatorPredecessorStep.nextStart, he, List.flatMap_nil, List.reverse_nil,
          List.map_nil, List.append_nil]
        rfl
      · have ht : (MessagePrefixLoop.find target rest).1 = some (previous, block) := by
          simpa only [MessagePrefixLoop.find, hm, ↓reduceIte] using hfind
        obtain ⟨before, after, htable, hbefore, hinput⟩ :=
          ih ((SimulatorLookup.entryBits entry).reverse.map some ++ beforeInput) ht
        refine ⟨entry :: before, after, ?_, ?_, ?_⟩
        · simp [htable]
        · intro e hin
          simp only [List.mem_cons] at hin
          rcases hin with rfl | hin
          · exact hm
          · exact hbefore e hin
        · rw [finish, if_neg hm, hinput]
          simp [List.flatMap_cons, List.reverse_append, List.map_append, List.append_assoc]

structure Input (n κ : Nat) where
  table : CompressionTable (Bits κ) (Bits n)
  target : Bits n
  beforeInput : List (Option Bool) := []
  beforeOutput : List (Option Bool) := []
  outputTail : List (Option Bool) := []

/-- A composable contract for the actual fixed-code search. Its result is the
complete physical machine state, not a host-decoded predecessor computation. -/
noncomputable def procedure (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) :
    TimedExecution.Procedure (Reification.timedStep (code n κ) oracle) (Input n κ) Machine.Configuration :=
  TimedExecution.Procedure.ofFixed _
    (fun (input : Input n κ) => NativeCode.frame state trace
      (start input.table input.target input.beforeInput input.beforeOutput input.outputTail))
    (fun _ out => NativeCode.frame state trace out)
    (fun (input : Input n κ) => PMF.pure (finish input.target input.beforeInput input.beforeOutput input.outputTail input.table))
    (fun (input : Input n κ) => steps input.target input.table)
    (fun (input : Input n κ) => by
      simpa only [PMF.pure_map] using run oracle state trace input.target input.table input.beforeInput input.beforeOutput input.outputTail)

theorem procedure_budget (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (input : Input n κ) :
    (procedure oracle state trace).budget input = steps input.target input.table := rfl

theorem procedure_costed (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (input : Input n κ) :
    (procedure oracle state trace).costed input =
      PMF.pure (finish input.target input.beforeInput input.beforeOutput input.outputTail input.table,
        steps input.target input.table) := by
  simp [procedure, TimedExecution.Procedure.ofFixed, PMF.pure_map]

theorem steps_positive (target : Bits n) (table : CompressionTable (Bits κ) (Bits n)) :
    0 < steps target table := by
  induction table with
  | nil => simp [steps]
  | cons entry rest ih =>
      simp only [steps]
      omega

/-- The final native halt has not run at this adjacent horizon. -/
theorem before_halt (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (target : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeInput beforeOutput outputTail : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (steps target table - 1)
      (NativeCode.frame state trace (start table target beforeInput beforeOutput outputTail)) =
      PMF.pure (NativeCode.frame state trace { finish target beforeInput beforeOutput outputTail table with halted := false }) := by
  induction table generalizing beforeInput with
  | nil =>
      have hp := SimulatorPredecessorStep.empty_before_halt (κ := κ) oracle state trace target beforeInput beforeOutput outputTail
      have he := SelectiveHaltReturn.active_eval (SimulatorPredecessorStep.code n κ) 0 (returns n κ) oracle
        (1 + (n + 1)) (NativeCode.frame state trace (SimulatorPredecessorStep.emptyStart target beforeInput beforeOutput outputTail))
        (by intro out hm; rw [hp, PMF.mem_support_pure_iff] at hm; subst out; rfl)
      have htime : n + 3 - 1 = 1 + (n + 1) := by omega
      change TimedExecution.eval _ (n + 3 - 1)
        (NativeCode.frame state trace (SimulatorPredecessorStep.emptyStart target beforeInput beforeOutput outputTail)) = _
      rw [htime, code, he, hp]
      rfl
  | cons entry rest ih =>
      have hstart : start (entry :: rest) target beforeInput beforeOutput outputTail =
          SimulatorPredecessorStep.entryStart entry target beforeInput beforeOutput
            ((SimulatorLookup.tableBits rest).map some) outputTail := by
        simp only [start, SimulatorPredecessorStep.entryStart, SimulatorLookup.tableBits_cons, List.map_append]
      by_cases hm : entry.1.2.1 = false ∧ entry.2 = target
      · have hp := SimulatorPredecessorStep.record_before_halt oracle state trace entry target beforeInput beforeOutput
          ((SimulatorLookup.tableBits rest).map some) outputTail
        have he := SelectiveHaltReturn.active_eval (SimulatorPredecessorStep.code n κ) 0 (returns n κ) oracle
          (SimulatorPredecessorStep.recordTime entry target)
          (NativeCode.frame state trace (SimulatorPredecessorStep.entryStart entry target beforeInput beforeOutput
            ((SimulatorLookup.tableBits rest).map some) outputTail))
          (by intro out hmem; rw [hp, PMF.mem_support_pure_iff] at hmem; subst out;
              exact SimulatorPredecessorStep.recordBefore_active _ _ _ _ _ _)
        rw [steps, if_pos hm, Nat.add_zero, Nat.add_sub_cancel, hstart, code, he, hp]
        rw [finish, if_pos hm]
        simp only [SimulatorPredecessorStep.recordBefore, hm.1, Bool.false_eq_true, ↓reduceIte, hm.2]
        rfl
      · have hr := record_run oracle state trace entry target beforeInput beforeOutput
          ((SimulatorLookup.tableBits rest).map some) outputTail
        have hn : SimulatorPredecessorStep.nextStart entry target beforeInput beforeOutput
            ((SimulatorLookup.tableBits rest).map some) outputTail =
            start rest target ((SimulatorLookup.entryBits entry).reverse.map some ++ beforeInput) beforeOutput outputTail := rfl
        have hp := steps_positive target rest
        rw [steps, if_neg hm,
          show SimulatorPredecessorStep.recordTime entry target + 1 + steps target rest - 1 =
            (SimulatorPredecessorStep.recordTime entry target + 1) + (steps target rest - 1) from by omega,
          hstart, TimedExecution.eval_add, hr, if_neg hm, PMF.pure_bind, hn, ih,
          finish, if_neg hm]

/-- Exact first native halt and complete retained state for the whole search. -/
theorem first_joint (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (target : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeInput beforeOutput outputTail : List (Option Bool)) :
    runToBoundary (Reification.timedStep (code n κ) oracle)
      (fun out => Reification.terminal out.control) (steps target table)
      (NativeCode.frame state trace (start table target beforeInput beforeOutput outputTail)) =
      PMF.pure (NativeCode.frame state trace (finish target beforeInput beforeOutput outputTail table), steps target table) := by
  have hp := before_halt oracle state trace target table beforeInput beforeOutput outputTail
  have hr := run oracle state trace target table beforeInput beforeOutput outputTail
  have hs := steps_positive target table
  have ht : steps target table - 1 + 1 = steps target table := by omega
  have h := runToBoundary_joint_of_adjacent (Reification.timedStep (code n κ) oracle)
    (fun out => Reification.terminal out.control)
    (NativeCode.frame state trace (start table target beforeInput beforeOutput outputTail))
    (steps target table - 1)
    (by intro out hterminal; simp [Reification.timedStep, hterminal])
    (by intro out hmem; rw [hp, PMF.mem_support_pure_iff] at hmem; subst out; rfl)
    (by intro out hmem; rw [ht, hr, PMF.mem_support_pure_iff] at hmem; subst out;
        exact finish_halted _ _ _ _ _)
  simpa only [ht, hr, PMF.pure_map] using h

/-- A public table-size cap gives a common horizon without changing the result. -/
theorem run_at_cap (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (target : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeInput beforeOutput outputTail : List (Option Bool))
    (cap : Nat) (hc : table.length ≤ cap) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle) (cap * (8 * n + 2 * κ + 14) + n + 3)
      (NativeCode.frame state trace (start table target beforeInput beforeOutput outputTail)) =
      PMF.pure (NativeCode.frame state trace (finish target beforeInput beforeOutput outputTail table)) := by
  have hb := steps_bound target table
  have hm := Nat.mul_le_mul_right (8 * n + 2 * κ + 14) hc
  have ht : steps target table ≤ cap * (8 * n + 2 * κ + 14) + n + 3 := by omega
  have ha : Reification.timedStep (code n κ) oracle
      (NativeCode.frame state trace (finish target beforeInput beforeOutput outputTail table)) =
      PMF.pure (NativeCode.frame state trace (finish target beforeInput beforeOutput outputTail table)) := by
    simp [Reification.timedStep, Reification.terminal, NativeCode.frame, finish_halted]
  rw [show cap * (8 * n + 2 * κ + 14) + n + 3 = steps target table +
      (cap * (8 * n + 2 * κ + 14) + n + 3 - steps target table) from by omega,
    TimedExecution.eval_add, run, PMF.pure_bind, TimedExecution.Block.eval_of_absorbing _ ha]

def encoding (E : FiniteBitEncoding State) :=
  EncodedStorage.codeEncoding.prod (ConfigurationEncoding.frame E)

def storageBound (n κ initialSize horizon : Nat) : Nat :=
  let b := initialSize + horizon * (EncodedStorage.addressCap (code n κ) + 3)
  2 * (EncodedStorage.codeEncoding.encode (code n κ)).length + 144 * b ^ 2 + 372 * b + 173

/-- Code, both physical tapes, opaque state and prior history at every supported
intermediate state; the external ideal oracle is never used by this search. -/
theorem encoded_peak (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (target : Bits n) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput outputTail : List (Option Bool))
    (horizon elapsed : Nat) (within : elapsed ≤ horizon) (out : Configuration State)
    (hs : out ∈ (TimedExecution.eval (Reification.timedStep (code n κ) oracle) elapsed
      (NativeCode.frame state trace (start table target beforeInput beforeOutput outputTail))).support) :
    ((encoding E).encode (code n κ, out)).length ≤
      storageBound n κ (NativePacketComponent.Resources.frameSize stateSize
        (NativeCode.frame state trace (start table target beforeInput beforeOutput outputTail))) horizon := by
  exact NativeCode.encoded_peak E stateSize hState oracle state trace (code n κ) (code_native n κ)
    (start table target beforeInput beforeOutput outputTail) horizon elapsed within out hs

theorem encoded_first (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (target : Bits n) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput outputTail : List (Option Bool)) (out : Configuration State × Nat)
    (hs : out ∈ (runToBoundary (Reification.timedStep (code n κ) oracle)
      (fun frame => Reification.terminal frame.control) (steps target table)
      (NativeCode.frame state trace (start table target beforeInput beforeOutput outputTail))).support) :
    ((encoding E).encode (code n κ, out.1)).length ≤
      storageBound n κ (NativePacketComponent.Resources.frameSize stateSize
        (NativeCode.frame state trace (start table target beforeInput beforeOutput outputTail))) out.2 := by
  exact encoded_peak E stateSize hState oracle state trace target table beforeInput beforeOutput outputTail
    out.2 out.2 (Nat.le_refl _) out.1 (runToBoundary_reachable _ _ _ _ out hs)

end Foundation.Hash.Native.SimulatorPredecessorLookup
