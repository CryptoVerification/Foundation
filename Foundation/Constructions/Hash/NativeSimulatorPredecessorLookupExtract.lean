import Foundation.Constructions.Hash.NativeSimulatorPredecessorExtract
import Foundation.Constructions.Hash.NativeIdealResources

/-! The successful ordered lookup exits by a real jump into key extraction.
The missing-predecessor halt is retained. This is one reconstruction update,
not yet the iterative IV/fuel controller. -/
namespace Foundation.Hash.Native.SimulatorPredecessorLookupExtract
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n κ : Nat}

def lookupCode (n κ : Nat) : Code :=
  SelectiveHaltReturn.code (SimulatorPredecessorLookup.code n κ)
    (SimulatorPredecessorLookup.code n κ).length
    (fun pc => pc == SimulatorPredecessorStep.foundPc n κ)

def code (n κ : Nat) (tail : Code) : Code :=
  CodeRelocation.host (lookupCode n κ) (SimulatorPredecessorExtract.code n κ tail)

theorem lookupCode_length (n κ : Nat) : (lookupCode n κ).length = (SimulatorPredecessorLookup.code n κ).length :=
  SelectiveHaltReturn.code_length _ _ _

theorem code_length (n κ : Nat) (tail : Code) :
    (code n κ tail).length = 14 * n + 18 * κ + 44 + tail.length := by
  rw [code, CodeRelocation.code_length, lookupCode_length,
    SimulatorPredecessorLookup.code_length, SimulatorPredecessorExtract.code_length]
  omega

theorem code_native (n κ : Nat) (tail : Code)
    (ht : ∀ op ∈ tail, ∃ native, op = .native native) :
    ∀ op ∈ code n κ tail, ∃ native, op = .native native :=
  CodeRelocation.host_native _ _
    (SelectiveHaltReturn.code_native _ _ _ (SimulatorPredecessorLookup.code_native n κ))
    (SimulatorPredecessorExtract.code_native n κ tail ht)

theorem found_cursor (target previous : Bits n) (block : Bits κ)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeInput beforeOutput suffix : List (Option Bool))
    (hf : (MessagePrefixLoop.find target table).1 = some (previous, block)) :
    (SimulatorPredecessorLookup.finish target beforeInput beforeOutput suffix table).pc = SimulatorPredecessorStep.foundPc n κ ∧
    (SimulatorPredecessorLookup.finish target beforeInput beforeOutput suffix table).outputTape =
      { left := target.toList.reverse.map some ++ beforeOutput, current := some true, right := suffix } := by
  induction table generalizing beforeInput with
  | nil => simp [MessagePrefixLoop.find] at hf
  | cons entry rest ih =>
      by_cases hm : entry.1.2.1 = false ∧ entry.2 = target
      · simp [SimulatorPredecessorLookup.finish, hm, SimulatorPredecessorStep.foundStart]
      · simp only [SimulatorPredecessorLookup.finish, hm, ↓reduceIte]
        apply ih
        simpa only [MessagePrefixLoop.find, hm, ↓reduceIte] using hf

theorem found_halt (n κ : Nat) :
    (SimulatorPredecessorLookup.code n κ)[SimulatorPredecessorStep.foundPc n κ]? = some (.native .halt) := by
  rw [SimulatorPredecessorLookup.code, SelectiveHaltReturn.lookup,
    SimulatorPredecessorStep.found_halt]
  simp [SelectiveHaltReturn.instruction, SimulatorPredecessorLookup.returns_found]

/-- Successful lookup returns into the continuation at its actual code address.
The last search halt is replaced, rather than followed by a host-side resume. -/
theorem lookup_return (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (target previous : Bits n) (block : Bits κ)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeInput suffix : List (Option Bool))
    (tail : Code) (hf : (MessagePrefixLoop.find target table).1 = some (previous, block)) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host (lookupCode n κ) tail) oracle)
      (SimulatorPredecessorLookup.steps target table)
      (NativeCode.frame state trace (SimulatorPredecessorLookup.start table target beforeInput [none] suffix)) =
      PMF.pure (CodeRelocation.frame (lookupCode n κ).length
        (NativeCode.frame state trace
          { SimulatorPredecessorLookup.finish target beforeInput [none] suffix table with pc := 0, halted := false })) := by
  have hp := SimulatorPredecessorLookup.before_halt oracle state trace target table beforeInput [none] suffix
  have hc := (found_cursor target previous block table beforeInput [none] suffix hf).1
  have hs := SimulatorPredecessorLookup.steps_positive target table
  have hr := SelectiveHaltReturn.return_run (SimulatorPredecessorLookup.code n κ)
    (SimulatorPredecessorLookup.code n κ).length (fun pc => pc == SimulatorPredecessorStep.foundPc n κ)
    oracle state trace (SimulatorPredecessorLookup.start table target beforeInput [none] suffix)
    { SimulatorPredecessorLookup.finish target beforeInput [none] suffix table with halted := false }
    (SimulatorPredecessorLookup.steps target table - 1) rfl hp
    (by simpa only [hc] using found_halt n κ) (by simp [hc])
  have ht : SimulatorPredecessorLookup.steps target table - 1 + 1 = SimulatorPredecessorLookup.steps target table := by omega
  rw [ht] at hr
  have ha := CodePrefixExecution.append_active (lookupCode n κ)
    (tail.map (CodeRelocation.instruction (lookupCode n κ).length)) oracle
    (SimulatorPredecessorLookup.steps target table)
    (NativeCode.frame state trace (SimulatorPredecessorLookup.start table target beforeInput [none] suffix))
    (by intro out hm; change out ∈ (TimedExecution.eval (Reification.timedStep (SelectiveHaltReturn.code _ _ _) oracle) _ _).support at hm; rw [hr, PMF.mem_support_pure_iff] at hm; subst out; rfl)
  rw [CodeRelocation.host, ha]
  simpa [lookupCode, SelectiveHaltReturn.code_length, CodeRelocation.frame, CodeRelocation.control,
    Machine.Configuration.rebasePc, Machine.Configuration.resumeAt, NativeCode.frame] using hr

/-- Search and extraction execute under one finite code. The witness identifies
the first matching physical record, with every preceding record retained. -/
theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (target previous : Bits n) (block : Bits κ)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeInput suffix : List (Option Bool))
    (tail : Code) (hf : (MessagePrefixLoop.find target table).1 = some (previous, block)) :
    ∃ before after,
      table = before ++ ((previous, (false, block)), target) :: after ∧
      (∀ entry ∈ before, ¬ (entry.1.2.1 = false ∧ entry.2 = target)) ∧
      TimedExecution.eval (Reification.timedStep (code n κ tail) oracle)
        (SimulatorPredecessorLookup.steps target table + (7 * n + 10 * κ + 13))
        (NativeCode.frame state trace (SimulatorPredecessorLookup.start table target beforeInput [none] suffix)) =
        PMF.pure (CodeRelocation.frame (code n κ []).length
          (NativeCode.frame state trace (SimulatorPredecessorExtract.finish previous target block
            ((before.flatMap SimulatorLookup.entryBits).reverse.map some ++ beforeInput)
            (ResponseLoading.fromCells ((SimulatorLookup.tableBits after).map some)).current
            (ResponseLoading.fromCells ((SimulatorLookup.tableBits after).map some)).right suffix))) := by
  obtain ⟨before, after, ht, hb, hi⟩ :=
    SimulatorPredecessorLookup.selected_layout target previous block table beforeInput [none] suffix hf
  refine ⟨before, after, ht, hb, ?_⟩
  have ho := (found_cursor target previous block table beforeInput [none] suffix hf).2
  have he : NativeCode.frame state trace
      { SimulatorPredecessorLookup.finish target beforeInput [none] suffix table with pc := 0, halted := false } =
      (⟨state, .running { inputTape := { left := (SimulatorLookup.entryBits ((previous, (false, block)), target)).reverse.map some ++ ((before.flatMap SimulatorLookup.entryBits).reverse.map some ++ beforeInput), current := (ResponseLoading.fromCells ((SimulatorLookup.tableBits after).map some)).current, right := (ResponseLoading.fromCells ((SimulatorLookup.tableBits after).map some)).right }, outputTape := SimulatorPredecessorExtract.scratch target suffix }, trace⟩ : Configuration State) := by
    simp [NativeCode.frame, hi, ho, FixedWidthCopy.frontier, SimulatorPredecessorExtract.scratch, List.append_assoc]
  have hl := lookup_return oracle state trace target previous block table beforeInput suffix
    (SimulatorPredecessorExtract.code n κ tail) hf
  rw [he] at hl
  have hx := SimulatorPredecessorExtract.run oracle state trace previous target block
    ((before.flatMap SimulatorLookup.entryBits).reverse.map some ++ beforeInput)
    (ResponseLoading.fromCells ((SimulatorLookup.tableBits after).map some)).current
    (ResponseLoading.fromCells ((SimulatorLookup.tableBits after).map some)).right suffix tail
  have h := SimulatorPredecessorExtract.seq_run oracle (lookupCode n κ)
    (SimulatorPredecessorExtract.code n κ tail) _ _ _ _ _ hl hx
  simpa only [code, CodeRelocation.frame, CodeRelocation.control, NativeCode.frame,
    Machine.Configuration.rebasePc, CodeRelocation.code_length, Nat.add_zero, Nat.add_assoc] using h

theorem steps_bound (target : Bits n) (table : CompressionTable (Bits κ) (Bits n)) :
    SimulatorPredecessorLookup.steps target table + (7 * n + 10 * κ + 13) ≤
      table.length * (8 * n + 2 * κ + 14) + 8 * n + 10 * κ + 16 := by
  have h := SimulatorPredecessorLookup.steps_bound target table
  omega

def targetMessage (target : Bits n) (suffix : List (Bits κ)) : Tape :=
  FixedWidthCopy.frontier [none]
    (target.toList.map some ++ none :: (FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some)

/-- The physical output is exactly the next raw target and the encoded
block-prepended suffix used by the reference reconstruction loop. -/
theorem finish_encoded (previous target : Bits n) (block : Bits κ) (suffix : List (Bits κ))
    (beforeInput : List (Option Bool)) (next : Option Bool) (rest : List (Option Bool)) :
    (SimulatorPredecessorExtract.finish previous target block beforeInput next rest
      ((FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some)).outputTape =
      targetMessage previous (block :: suffix) := by
  rw [SimulatorPredecessorExtract.finish_output]
  simp [targetMessage, FiniteBitEncoding.encodeList, SimulatorPredecessorExtract.payload,
    fixedBits, Foundation.Encoding.vector, Bits.toList, List.map_append, List.append_assoc]

/-- One successful reference step and its instruction-level implementation have
the same target/suffix update, including ordered collision selection. -/
theorem reconstruct_step (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial target previous : Bits n) (block : Bits κ)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeInput : List (Option Bool))
    (suffix : List (Bits κ)) (fuel : Nat) (tail : Code)
    (hf : (MessagePrefixLoop.find target table).1 = some (previous, block)) (hn : target ≠ initial) :
    (MessagePrefixLoop.run initial table (fuel + 1) target suffix).message =
      (MessagePrefixLoop.run initial table fuel previous (block :: suffix)).message ∧
    ∃ result : Machine.Configuration,
      result.outputTape = targetMessage previous (block :: suffix) ∧
      TimedExecution.eval (Reification.timedStep (code n κ tail) oracle)
        (SimulatorPredecessorLookup.steps target table + (7 * n + 10 * κ + 13))
        (NativeCode.frame state trace (SimulatorPredecessorLookup.start table target beforeInput [none]
          ((FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some))) =
        PMF.pure (CodeRelocation.frame (code n κ []).length (NativeCode.frame state trace result)) := by
  constructor
  · simp [MessagePrefixLoop.run, hf, hn]
  · obtain ⟨before, after, _, _, hr⟩ := run oracle state trace target previous block table beforeInput
      ((FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some) tail hf
    exact ⟨_, finish_encoded _ _ _ _ _ _ _, hr⟩

theorem missing_cursor (target : Bits n) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput suffix : List (Option Bool))
    (hf : (MessagePrefixLoop.find target table).1 = none) :
    (SimulatorPredecessorLookup.finish target beforeInput beforeOutput suffix table).pc =
      SimulatorPredecessorStep.missingPc n κ := by
  induction table generalizing beforeInput with
  | nil => rfl
  | cons entry rest ih =>
      by_cases hm : entry.1.2.1 = false ∧ entry.2 = target
      · simp [MessagePrefixLoop.find, hm] at hf
      · simp only [SimulatorPredecessorLookup.finish, hm, ↓reduceIte]
        apply ih
        simpa only [MessagePrefixLoop.find, hm, ↓reduceIte] using hf

/-- Missing predecessors still execute the retained halt; extraction never runs. -/
theorem missing_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (target : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (beforeInput suffix : List (Option Bool))
    (tail : Code) (hf : (MessagePrefixLoop.find target table).1 = none) :
    TimedExecution.eval (Reification.timedStep (code n κ tail) oracle)
      (SimulatorPredecessorLookup.steps target table)
      (NativeCode.frame state trace (SimulatorPredecessorLookup.start table target beforeInput [none] suffix)) =
      PMF.pure (NativeCode.frame state trace (SimulatorPredecessorLookup.finish target beforeInput [none] suffix table)) := by
  have hp := SimulatorPredecessorLookup.before_halt oracle state trace target table beforeInput [none] suffix
  have hc := missing_cursor target table beforeInput [none] suffix hf
  have hs := SimulatorPredecessorLookup.steps_positive target table
  have hh : (SimulatorPredecessorLookup.code n κ)[SimulatorPredecessorStep.missingPc n κ]? = some (.native .halt) := by
    rw [SimulatorPredecessorLookup.code, SelectiveHaltReturn.lookup, SimulatorPredecessorStep.missing_halt]
    simp [SelectiveHaltReturn.instruction, SimulatorPredecessorLookup.returns_missing]
  have hn : SimulatorPredecessorStep.missingPc n κ ≠ SimulatorPredecessorStep.foundPc n κ := by
    obtain ⟨hfound, _, _, hmissing⟩ := SimulatorPredecessorStep.pc_formulas n κ
    omega
  have he := SelectiveHaltReturn.active_eval (SimulatorPredecessorLookup.code n κ)
    (SimulatorPredecessorLookup.code n κ).length (fun pc => pc == SimulatorPredecessorStep.foundPc n κ)
    oracle (SimulatorPredecessorLookup.steps target table - 1)
    (NativeCode.frame state trace (SimulatorPredecessorLookup.start table target beforeInput [none] suffix))
    (by intro out hm; rw [hp, PMF.mem_support_pure_iff] at hm; subst out; rfl)
  have ha := CodePrefixExecution.append_active (lookupCode n κ)
    ((SimulatorPredecessorExtract.code n κ tail).map (CodeRelocation.instruction (lookupCode n κ).length)) oracle
    (SimulatorPredecessorLookup.steps target table - 1)
    (NativeCode.frame state trace (SimulatorPredecessorLookup.start table target beforeInput [none] suffix))
    (by intro out hm; change out ∈ (TimedExecution.eval (Reification.timedStep (SelectiveHaltReturn.code _ _ _) oracle) _ _).support at hm; rw [he, hp, PMF.mem_support_pure_iff] at hm; subst out; rfl)
  have fetch : (code n κ tail)[SimulatorPredecessorStep.missingPc n κ]? = some (.native .halt) := by
    have hi : SimulatorPredecessorStep.missingPc n κ < (lookupCode n κ).length := by
      rw [lookupCode_length]
      exact List.getElem?_eq_some_iff.mp hh |>.1
    rw [code, CodeRelocation.host, List.getElem?_append_left hi, lookupCode, SelectiveHaltReturn.lookup, hh]
    simp [SelectiveHaltReturn.instruction, hn]
  rw [show SimulatorPredecessorLookup.steps target table = (SimulatorPredecessorLookup.steps target table - 1) + 1 from by omega,
    TimedExecution.eval_add]
  change (TimedExecution.eval (Reification.timedStep ((lookupCode n κ) ++ _ ) oracle) _ _).bind _ = _
  rw [ha]
  change (TimedExecution.eval (Reification.timedStep (SelectiveHaltReturn.code _ _ _) oracle) _ _).bind _ = _
  rw [he, hp, PMF.pure_bind]
  have hhalt := SimulatorPredecessorLookup.finish_halted target table beforeInput [none] suffix
  simp only [TimedExecution.eval, Reification.timedStep, Reification.terminal, NativeCode.frame,
    Bool.false_eq_true, ↓reduceIte, Reification.perform, Reification.action, transition,
    hc, fetch, Machine.Instruction.next, PMF.pure_bind]
  cases hm : SimulatorPredecessorLookup.finish target beforeInput [none] suffix table
  simp only [hm] at hc hhalt
  simp_all

end Foundation.Hash.Native.SimulatorPredecessorLookupExtract
