import Foundation.Constructions.Hash.NativeSimulatorPredecessorLookupExtract
import Foundation.Crypto.Semantics.Oracle.ForwardConstantCheck
import Foundation.Crypto.Semantics.Oracle.UnaryFuel

/-! Finite-code predecessor reconstruction. Fuel is a unary input-tape field,
not code expansion. The IV guard is executed before fuel consumption. -/
namespace Foundation.Hash.Native.SimulatorReconstruct
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n κ : Nat}

def accepted : Code := [.native (.write .output true), .native .halt]
def failed (n : Nat) : Code :=
  StraightLine.code (List.replicate n (.right .output) ++ [.write .output (some false)]) ++ [.native .halt]
def rewind : Code := LeftBlankRewind.code .input [.native .halt]
def next (n κ : Nat) : Code := SimulatorPredecessorLookupExtract.code n κ rewind
def source (initial : Bits n) (κ : Nat) : Code :=
  ForwardConstantCheck.code initial.toList accepted
    (ForwardConstantCheck.recover (UnaryFuel.code (next n κ) (failed n)))
def guardPrefix (initial : Bits n) : Code := ForwardConstantCheck.rejectedPrefix initial.toList accepted
def restartPc (initial : Bits n) (κ : Nat) : Nat :=
  (guardPrefix initial).length + 5 + 11 + (SimulatorPredecessorLookupExtract.code n κ []).length + 4
def code (initial : Bits n) (κ : Nat) : Code :=
  SelectiveHaltReturn.code (source initial κ) 0 (fun pc => pc == restartPc initial κ)

def startWith (savedContext : List (Option Bool)) (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat)
    (target : Bits n) (suffix : List (Bits κ)) : Machine.Configuration :=
  { inputTape := UnaryFuel.tapeWith savedContext fuel used ((SimulatorLookup.tableBits table).map some),
    outputTape := SimulatorPredecessorLookupExtract.targetMessage target suffix }

def start (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat)
    (target : Bits n) (suffix : List (Bits κ)) : Machine.Configuration := startWith [] table fuel used target suffix

theorem source_length (initial : Bits n) (κ : Nat) : (source initial κ).length = 17 * n + 18 * κ + 69 := by
  simp [source, ForwardConstantCheck.code, ForwardConstantCheck.compareCode_length,
    ForwardConstantCheck.recover, CodeRelocation.code_length, UnaryFuel.code, UnaryFuel.body_length,
    next, SimulatorPredecessorLookupExtract.code_length, rewind, LeftBlankRewind.code,
    LeftBlankRewind.body_length, accepted, failed, StraightLine.code]
  omega

theorem code_length (initial : Bits n) (κ : Nat) : (code initial κ).length = 17 * n + 18 * κ + 69 := by
  rw [code, SelectiveHaltReturn.code_length, source_length]

theorem restartPc_eq (initial : Bits n) (κ : Nat) : restartPc initial κ = 16 * n + 18 * κ + 66 := by
  simp [restartPc, guardPrefix, ForwardConstantCheck.rejectedPrefix, CodeRelocation.code_length,
    ForwardConstantCheck.compareCode_length, accepted, SimulatorPredecessorLookupExtract.code_length]
  omega

theorem source_native (initial : Bits n) (κ : Nat) :
    ∀ op ∈ source initial κ, ∃ native, op = .native native := by
  have halt : ∀ op ∈ ([.native .halt] : Code), ∃ native, op = .native native := by
    intro op hm; exact ⟨_, by simpa using hm⟩
  have hrew : ∀ op ∈ rewind, ∃ native, op = .native native :=
    CodeRelocation.host_native _ _ (LeftBlankRewind.body_native _) halt
  have hfail : ∀ op ∈ failed n, ∃ native, op = .native native := by
    intro op hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨action, _, rfl⟩ := List.mem_map.mp hm
      exact ⟨_, rfl⟩
    · exact halt op hm
  apply ForwardConstantCheck.code_native
  · intro op hm
    simp only [accepted, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> exact ⟨_, rfl⟩
  apply CodeRelocation.host_native
  · intro op hm; exact ⟨_, by simpa using hm⟩
  apply CodeRelocation.host_native
  · exact LeftBlankRewind.body_native _
  exact UnaryFuel.code_native _ _ (SimulatorPredecessorLookupExtract.code_native _ _ _ hrew) hfail

theorem code_native (initial : Bits n) (κ : Nat) :
    ∀ op ∈ code initial κ, ∃ native, op = .native native :=
  SelectiveHaltReturn.code_native _ _ _ (source_native initial κ)

theorem table_nonempty (table : CompressionTable (Bits κ) (Bits n)) : SimulatorLookup.tableBits table ≠ [] := by
  simp [SimulatorLookup.tableBits]

def flagTape (target : Bits n) (suffix : List (Bits κ)) (flag : Bool) : Tape :=
  { left := target.toList.reverse.map some ++ [none], current := some flag,
    right := (FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some }

section SavedContext
variable {savedContext : List (Option Bool)}
local notation "start" => startWith savedContext

theorem accepted_before (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat) (suffix : List (Bits κ)) :
    TimedExecution.eval (Reification.timedStep (source initial κ) oracle) (2 * n + 1)
      (NativeCode.frame state trace (start table fuel used initial suffix)) =
      PMF.pure (NativeCode.frame state trace
        { pc := 2 * n + 1, inputTape := (start table fuel used initial suffix).inputTape,
          outputTape := flagTape initial suffix true }) := by
  have hr := ForwardConstantCheck.match_run oracle state trace accepted.length
    (CodeRelocation.host accepted (ForwardConstantCheck.recover (UnaryFuel.code (next n κ) (failed n))))
    (start table fuel used initial suffix).inputTape initial.toList [none]
    (none :: (FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some)
  simp only [Bits.length_toList] at hr
  rw [show 2 * n + 1 = 2 * n + 1 from rfl, TimedExecution.eval_add]
  change (TimedExecution.eval (Reification.timedStep (ForwardConstantCheck.compareCode _ _ _) oracle) _ _).bind _ = _
  simp only [startWith, SimulatorPredecessorLookupExtract.targetMessage] at hr ⊢
  rw [hr, PMF.pure_bind]
  rw [source, ForwardConstantCheck.code, ForwardConstantCheck.link]
  have placed := CodeRelocation.eval (ForwardConstantCheck.compareCode accepted.length [] initial.toList)
    (CodeRelocation.host accepted (ForwardConstantCheck.recover (UnaryFuel.code (next n κ) (failed n)))) oracle 1
    (NativeCode.frame state trace { inputTape := (start table fuel used initial suffix).inputTape, outputTape := FixedWidthCopy.frontier (initial.toList.reverse.map some ++ [none]) (none :: (FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some) })
  simp only [ForwardConstantCheck.compareCode_length, Bits.length_toList, List.length_nil, Nat.add_zero, startWith] at placed
  rw [placed]
  simp [accepted, CodeRelocation.host, NativeCode.frame, TimedExecution.eval,
    Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
    transition, Machine.Instruction.next, Machine.Configuration.advance,
    Machine.Configuration.updateTape, FixedWidthCopy.frontier, ResponseLoading.fromCells,
    Tape.write, flagTape, PMF.pure_map, CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc]

def recoveryPrefix : Code :=
  CodeRelocation.host [.native (.moveLeft .output)] (LeftBlankRewind.body .output)
def fuelPrefix (initial : Bits n) : Code := CodeRelocation.host (guardPrefix initial) recoveryPrefix

theorem source_fuel_host (initial : Bits n) :
    source initial κ = CodeRelocation.host (fuelPrefix initial) (UnaryFuel.code (next n κ) (failed n)) := by
  rw [source, ForwardConstantCheck.rejected_host]
  simp only [ForwardConstantCheck.recover, LeftBlankRewind.code, fuelPrefix, recoveryPrefix, guardPrefix,
    CodeRelocation.host_assoc]

theorem rejected_prepare (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial target : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat) (suffix : List (Bits κ))
    (hn : target ≠ initial) :
    ∃ k, k < n ∧
      TimedExecution.eval (Reification.timedStep (source initial κ) oracle) (5 * k + 4)
        (NativeCode.frame state trace (start table fuel used target suffix)) =
        PMF.pure (CodeRelocation.frame (fuelPrefix initial).length
          (NativeCode.frame state trace (start table fuel used target suffix))) := by
  have hne : initial.toList ≠ target.toList := by
    intro he
    exact hn (List.ofFn_injective he).symm
  obtain ⟨k, hk, hr⟩ := ForwardConstantCheck.rejected_run oracle state trace initial.toList target.toList
    accepted (UnaryFuel.code (next n κ) (failed n)) (start table fuel used target suffix).inputTape
    (none :: (FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some) (by simp) hne
  refine ⟨k, by simpa using hk, ?_⟩
  simpa only [source, startWith, SimulatorPredecessorLookupExtract.targetMessage, fuelPrefix,
    recoveryPrefix, guardPrefix, CodeRelocation.code_length, LeftBlankRewind.body_length,
    List.length_cons, List.length_nil] using hr

theorem tableCells (table : CompressionTable (Bits κ) (Bits n)) :
    (ResponseLoading.fromCells ((SimulatorLookup.tableBits table).map some)).current ::
      (ResponseLoading.fromCells ((SimulatorLookup.tableBits table).map some)).right =
      (SimulatorLookup.tableBits table).map some := by
  have hn : (SimulatorLookup.tableBits table).map some ≠ [] := by simpa using table_nonempty table
  generalize (SimulatorLookup.tableBits table).map some = cells at hn ⊢
  cases cells <;> simp_all [ResponseLoading.fromCells]

theorem tableBits_append (before after : CompressionTable (Bits κ) (Bits n)) :
    SimulatorLookup.tableBits (before ++ after) = before.flatMap SimulatorLookup.entryBits ++ SimulatorLookup.tableBits after := by
  simp [SimulatorLookup.tableBits, List.flatMap_append, List.append_assoc]

/-- The selected record and all passed records are physically rewound before
the restart site is reached. The saved suffix and unary fuel survive the scan. -/
theorem next_before_restart (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (target previous : Bits n) (block : Bits κ)
    (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat) (suffix : List (Bits κ))
    (hf : (MessagePrefixLoop.find target table).1 = some (previous, block)) :
    ∃ before after,
      table = before ++ ((previous, (false, block)), target) :: after ∧
      TimedExecution.eval (Reification.timedStep (next n κ) oracle)
        (SimulatorPredecessorLookup.steps target table + (7 * n + 10 * κ + 13) +
          (3 * (before.flatMap SimulatorLookup.entryBits).length + 5))
        (NativeCode.frame state trace (start table fuel used target suffix)) =
        PMF.pure (CodeRelocation.frame ((SimulatorPredecessorLookupExtract.code n κ []).length + 4)
          (NativeCode.frame state trace (start table fuel used previous (block :: suffix)))) := by
  let counter := UnaryFuel.counterWith savedContext fuel used
  let saved := (FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some
  obtain ⟨before, after, ht, _, hr⟩ := SimulatorPredecessorLookupExtract.run oracle state trace target previous block table
    (none :: counter) saved rewind hf
  refine ⟨before, after, ht, ?_⟩
  let past := before.flatMap SimulatorLookup.entryBits
  let remaining := (SimulatorPredecessorFilter.escaped previous.toList).map some ++ [some true, some false] ++
    (SimulatorPredecessorExtract.payload block).map some ++ target.toList.map some ++ (SimulatorLookup.tableBits after).map some
  let extracted := SimulatorPredecessorExtract.finish previous target block
    (past.reverse.map some ++ none :: counter)
    (ResponseLoading.fromCells ((SimulatorLookup.tableBits after).map some)).current
    (ResponseLoading.fromCells ((SimulatorLookup.tableBits after).map some)).right saved
  have hi : extracted.inputTape = FixedWidthCopy.backwardFrontier remaining
      ((true :: past.reverse).map some ++ none :: counter) := by
    simp [extracted, SimulatorPredecessorExtract.finish_input, remaining, past, tableCells,
      FixedWidthCopy.backwardFrontier, List.append_assoc]
  have ho : extracted.outputTape = SimulatorPredecessorLookupExtract.targetMessage previous (block :: suffix) :=
    SimulatorPredecessorLookupExtract.finish_encoded _ _ _ _ _ _ _
  have hbits : (true :: past.reverse).reverse.map some ++ remaining = (SimulatorLookup.tableBits table).map some := by
    rw [ht, tableBits_append, SimulatorLookup.tableBits_cons]
    simp [past, remaining, SimulatorPredecessorExtract.entry_layout, SimulatorPredecessorExtract.prePayload,
      List.reverse_cons, List.map_append, List.append_assoc]
  have hw := LeftBlankRewind.run oracle state trace .input [.native .halt] (true :: past.reverse)
    remaining counter (SimulatorPredecessorLookupExtract.targetMessage previous (block :: suffix))
  simp only [LeftBlankRewind.put, hbits, List.length_cons, List.length_reverse] at hw
  have hx : NativeCode.frame state trace extracted =
      NativeCode.frame state trace (LeftBlankRewind.put .input (FixedWidthCopy.backwardFrontier remaining
        ((true :: past.reverse).map some ++ none :: counter)) (SimulatorPredecessorLookupExtract.targetMessage previous (block :: suffix))) := by
    have hp : extracted.pc = 0 := rfl
    have hh : extracted.halted = false := rfl
    cases hm : extracted
    simp only [hm] at hi ho hp hh
    simp_all [NativeCode.frame, LeftBlankRewind.put]
  have hprefix : next n κ = CodeRelocation.host (SimulatorPredecessorLookupExtract.code n κ []) rewind := by
    simp only [next, SimulatorPredecessorLookupExtract.code, SimulatorPredecessorExtract.code]
    simp only [← CodeRelocation.host_assoc]
    simp [CodeRelocation.host]
  rw [show start table fuel used target suffix = SimulatorPredecessorLookup.start table target (none :: counter) [none] saved from rfl]
  rw [TimedExecution.eval_add, show next n κ = SimulatorPredecessorLookupExtract.code n κ rewind from rfl, hr, PMF.pure_bind]
  rw [hx]
  rw [show SimulatorPredecessorLookupExtract.code n κ rewind = CodeRelocation.host (SimulatorPredecessorLookupExtract.code n κ []) rewind from hprefix, CodeRelocation.eval]
  have htime : 3 * past.length + 5 = 3 * (past.length + 1) + 2 := by omega
  rw [htime]
  simp only [rewind, LeftBlankRewind.put]
  rw [hw, PMF.pure_map]
  simp only [startWith, UnaryFuel.tapeWith, counter, CodeRelocation.frame, CodeRelocation.control,
    NativeCode.frame, Machine.Configuration.rebasePc, Nat.add_zero]

def searchPrefix (initial : Bits n) (κ : Nat) : Code :=
  CodeRelocation.host (fuelPrefix initial) (UnaryFuel.body (11 + (next n κ).length))

theorem source_search_host (initial : Bits n) :
    source initial κ = CodeRelocation.host (searchPrefix initial κ) (CodeRelocation.host (next n κ) (failed n)) := by
  rw [source_fuel_host, UnaryFuel.code, ← CodeRelocation.host_assoc]; rfl

theorem restart_offset (initial : Bits n) :
    restartPc initial κ = (searchPrefix initial κ).length +
      ((SimulatorPredecessorLookupExtract.code n κ []).length + 4) := by
  simp [restartPc, searchPrefix, fuelPrefix, recoveryPrefix, CodeRelocation.code_length,
    UnaryFuel.body_length, LeftBlankRewind.body_length, Nat.add_assoc]

theorem begin_search (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial target : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat) (suffix : List (Bits κ))
    (hn : target ≠ initial) :
    ∃ k, k < n ∧
      TimedExecution.eval (Reification.timedStep (source initial κ) oracle) ((5 * k + 4) + (6 * used + 7))
        (NativeCode.frame state trace (start table (fuel + 1) used target suffix)) =
        PMF.pure (CodeRelocation.frame (searchPrefix initial κ).length
          (NativeCode.frame state trace (start table fuel (used + 1) target suffix))) := by
  obtain ⟨k, hk, hp⟩ := rejected_prepare (savedContext := savedContext) oracle state trace initial target table (fuel + 1) used suffix hn
  refine ⟨k, hk, ?_⟩
  have hne : (SimulatorLookup.tableBits table).map some ≠ [] := by simpa using table_nonempty table
  cases hc : (SimulatorLookup.tableBits table).map some with
  | nil => contradiction
  | cons head rest =>
      have hf := UnaryFuel.consume_run (savedContext := savedContext) oracle state trace (next n κ) (failed n) fuel used head rest
        (SimulatorPredecessorLookupExtract.targetMessage target suffix)
      have hf' : TimedExecution.eval (Reification.timedStep (UnaryFuel.code (next n κ) (failed n)) oracle)
          (6 * used + 7) (NativeCode.frame state trace (start table (fuel + 1) used target suffix)) =
          PMF.pure (CodeRelocation.frame 11 (NativeCode.frame state trace (start table fuel (used + 1) target suffix))) := by
        simpa only [startWith, hc, UnaryFuel.cursor] using hf
      rw [source_fuel_host] at hp ⊢
      have h := SimulatorPredecessorExtract.seq_run oracle (fuelPrefix initial) _ _ _ _ _ _ hp hf'
      simpa only [searchPrefix, CodeRelocation.code_length, UnaryFuel.body_length,
        CodeRelocation.frame, CodeRelocation.control, NativeCode.frame, Machine.Configuration.rebasePc,
        Nat.add_zero, Nat.add_assoc] using h

theorem next_host : next n κ = CodeRelocation.host (SimulatorPredecessorLookupExtract.code n κ []) rewind := by
  simp only [next, SimulatorPredecessorLookupExtract.code, SimulatorPredecessorExtract.code,
    ← CodeRelocation.host_assoc]
  simp [CodeRelocation.host]

theorem next_restart_halt : (next n κ)[(SimulatorPredecessorLookupExtract.code n κ []).length + 4]? = some (.native .halt) := by
  rw [next_host, CodeRelocation.lookup]
  have hr : rewind[4]? = some (.native .halt) := by
    rw [rewind, LeftBlankRewind.code]
    change (CodeRelocation.host (LeftBlankRewind.body .input) [.native .halt])[(LeftBlankRewind.body .input).length + 0]? = _
    rw [CodeRelocation.lookup]; rfl
  rw [hr]; rfl

theorem restart_halt (initial : Bits n) : (source initial κ)[restartPc initial κ]? = some (.native .halt) := by
  rw [source_search_host, restart_offset, CodeRelocation.lookup]
  have hi : (SimulatorPredecessorLookupExtract.code n κ []).length + 4 < (next n κ).length :=
    (List.getElem?_eq_some_iff.mp next_restart_halt).1
  rw [CodeRelocation.host, List.getElem?_append_left hi, next_restart_halt]
  rfl

/-- One consumed unit of tape fuel, one actual table search/extraction, a real
table rewind, and the executed back-edge to the IV guard. -/
theorem cycle_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial target previous : Bits n) (block : Bits κ)
    (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat) (suffix : List (Bits κ))
    (hn : target ≠ initial) (hf : (MessagePrefixLoop.find target table).1 = some (previous, block)) :
    ∃ k before after,
      k < n ∧ table = before ++ ((previous, (false, block)), target) :: after ∧
      TimedExecution.eval (Reification.timedStep (code initial κ) oracle)
        (((5 * k + 4) + (6 * used + 7)) +
          (SimulatorPredecessorLookup.steps target table + (7 * n + 10 * κ + 13) +
            (3 * (before.flatMap SimulatorLookup.entryBits).length + 5)) + 1)
        (NativeCode.frame state trace (start table (fuel + 1) used target suffix)) =
        PMF.pure (NativeCode.frame state trace (start table fuel (used + 1) previous (block :: suffix))) := by
  obtain ⟨k, hk, hp⟩ := begin_search (savedContext := savedContext) oracle state trace initial target table fuel used suffix hn
  obtain ⟨before, after, ht, hs⟩ := next_before_restart (savedContext := savedContext) oracle state trace target previous block table fuel (used + 1) suffix hf
  refine ⟨k, before, after, hk, ht, ?_⟩
  have ha := CodePrefixExecution.append_active (next n κ)
    ((failed n).map (CodeRelocation.instruction (next n κ).length)) oracle
    (SimulatorPredecessorLookup.steps target table + (7 * n + 10 * κ + 13) +
      (3 * (before.flatMap SimulatorLookup.entryBits).length + 5))
    (NativeCode.frame state trace (start table fuel (used + 1) target suffix))
    (by intro out hm; rw [hs, PMF.mem_support_pure_iff] at hm; subst out; rfl)
  have hs' : TimedExecution.eval (Reification.timedStep (CodeRelocation.host (next n κ) (failed n)) oracle)
      (SimulatorPredecessorLookup.steps target table + (7 * n + 10 * κ + 13) + (3 * (before.flatMap SimulatorLookup.entryBits).length + 5))
      (NativeCode.frame state trace (start table fuel (used + 1) target suffix)) =
      PMF.pure (CodeRelocation.frame ((SimulatorPredecessorLookupExtract.code n κ []).length + 4)
        (NativeCode.frame state trace (start table fuel (used + 1) previous (block :: suffix)))) := by
    rw [CodeRelocation.host, ha, hs]
  rw [source_search_host] at hp
  have h := SimulatorPredecessorExtract.seq_run oracle (searchPrefix initial κ) _ _ _ _ _ _ hp hs'
  let result := { start table fuel (used + 1) previous (block :: suffix) with pc := restartPc initial κ }
  have hresult : CodeRelocation.frame (searchPrefix initial κ).length
      (CodeRelocation.frame ((SimulatorPredecessorLookupExtract.code n κ []).length + 4)
        (NativeCode.frame state trace (start table fuel (used + 1) previous (block :: suffix)))) = NativeCode.frame state trace result := by
    simp [result, NativeCode.frame, CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc,
      restart_offset, startWith]
  rw [hresult, ← source_search_host] at h
  have hr := SelectiveHaltReturn.return_run (source initial κ) 0 (fun pc => pc == restartPc initial κ)
    oracle state trace (start table (fuel + 1) used target suffix) result _ rfl h
    (by simpa [result] using restart_halt (κ := κ) initial) (by simp [result])
  simpa only [code, result, Machine.Configuration.resumeAt, startWith] using hr

theorem retained_halt (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial : Bits n)
    (entry before : Machine.Configuration) (time : Nat) (ha : before.halted = false)
    (hr : TimedExecution.eval (Reification.timedStep (source initial κ) oracle) time
      (NativeCode.frame state trace entry) = PMF.pure (NativeCode.frame state trace before))
    (hh : (source initial κ)[before.pc]? = some (.native .halt)) (hn : before.pc ≠ restartPc initial κ) :
    TimedExecution.eval (Reification.timedStep (code initial κ) oracle) (time + 1)
      (NativeCode.frame state trace entry) = PMF.pure (NativeCode.frame state trace { before with halted := true }) :=
  SelectiveHaltReturn.halt_run _ _ _ oracle state trace entry before time ha hr hh (by simp [hn])

theorem accepted_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat) (suffix : List (Bits κ)) :
    TimedExecution.eval (Reification.timedStep (code initial κ) oracle) (2 * n + 2)
      (NativeCode.frame state trace (start table fuel used initial suffix)) =
      PMF.pure (NativeCode.frame state trace
        { pc := 2 * n + 1, inputTape := (start table fuel used initial suffix).inputTape,
          outputTape := flagTape initial suffix true, halted := true }) := by
  have hh : (source initial κ)[2 * n + 1]? = some (.native .halt) := by
    rw [source, ForwardConstantCheck.code, ForwardConstantCheck.link]
    have hl : (ForwardConstantCheck.compareCode accepted.length [] initial.toList).length = 2 * n := by
      simp [ForwardConstantCheck.compareCode_length]
    rw [← hl, CodeRelocation.lookup]
    have hg : (CodeRelocation.host accepted (ForwardConstantCheck.recover (UnaryFuel.code (next n κ) (failed n))))[1]? = some (.native .halt) := by
      simp [accepted, CodeRelocation.host]
    rw [hg]; rfl
  have hn : 2 * n + 1 ≠ restartPc initial κ := by rw [restartPc_eq]; omega
  have h := retained_halt oracle state trace initial _ _ _ rfl
    (accepted_before (savedContext := savedContext) oracle state trace initial table fuel used suffix) hh hn
  simpa only [show 2 * n + 1 + 1 = 2 * n + 2 by omega] using h

theorem failed_before (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (target : Bits n) (suffix : List (Bits κ)) (input : Tape) :
    TimedExecution.eval (Reification.timedStep (failed n) oracle) (n + 1)
      (NativeCode.frame state trace { inputTape := input, outputTape := SimulatorPredecessorLookupExtract.targetMessage target suffix }) =
      PMF.pure (NativeCode.frame state trace { pc := n + 1, inputTape := input, outputTape := flagTape target suffix false }) := by
  have h := StraightLine.public_run oracle state trace [] [.native .halt]
    (List.replicate n (.right .output) ++ [.write .output (some false)])
    { inputTape := input, outputTape := SimulatorPredecessorLookupExtract.targetMessage target suffix } rfl rfl
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil,
    List.nil_append, StraightLine.execute_append] at h
  have hm := FixedWidthCopy.advance_output target.toList [none]
    (none :: (FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some) ({ inputTape := input } : Machine.Configuration)
  simp only [Bits.length_toList] at hm
  change StraightLine.execute (List.replicate n (.right .output))
      { inputTape := input, outputTape := SimulatorPredecessorLookupExtract.targetMessage target suffix } = _ at hm
  rw [hm] at h
  simpa [failed, flagTape, NativeCode.frame, StraightLine.execute, StraightLine.apply,
    Machine.Configuration.updateTape, Machine.Configuration.advance, FixedWidthCopy.frontier,
    ResponseLoading.fromCells, Tape.write] using h

def emptyPrefix (initial : Bits n) (κ : Nat) : Code :=
  CodeRelocation.host (searchPrefix initial κ) (next n κ)

theorem source_empty_host (initial : Bits n) : source initial κ = CodeRelocation.host (emptyPrefix initial κ) (failed n) := by
  rw [source_search_host, ← CodeRelocation.host_assoc]; rfl

theorem failed_length (n : Nat) : (failed n).length = n + 2 := by simp [failed, StraightLine.code]
theorem failed_halt (n : Nat) : (failed n)[n + 1]? = some (.native .halt) := by
  have hl : (StraightLine.code (List.replicate n (.right .output) ++ [.write .output (some false)])).length = n + 1 := by
    simp [StraightLine.code]
  rw [failed, ← hl, List.getElem?_append_right (by omega)]
  simp

theorem empty_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial target : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (used : Nat) (suffix : List (Bits κ)) (hn : target ≠ initial) :
    ∃ k, k < n ∧
      TimedExecution.eval (Reification.timedStep (code initial κ) oracle) ((5 * k + 4) + (3 * used + 3) + (n + 2))
        (NativeCode.frame state trace (start table 0 used target suffix)) =
        PMF.pure (NativeCode.frame state trace
          { pc := (emptyPrefix initial κ).length + (n + 1),
            inputTape := { left := savedContext, current := none, right := List.replicate used (some false) ++ none :: (SimulatorLookup.tableBits table).map some },
            outputTape := flagTape target suffix false, halted := true }) := by
  obtain ⟨k, hk, hp⟩ := rejected_prepare (savedContext := savedContext) oracle state trace initial target table 0 used suffix hn
  refine ⟨k, hk, ?_⟩
  have hne : (SimulatorLookup.tableBits table).map some ≠ [] := by simpa using table_nonempty table
  let input : Tape := { left := savedContext, current := none, right := List.replicate used (some false) ++ none :: (SimulatorLookup.tableBits table).map some }
  have hf : TimedExecution.eval (Reification.timedStep (UnaryFuel.code (next n κ) (failed n)) oracle)
      (3 * used + 3) (NativeCode.frame state trace (start table 0 used target suffix)) =
      PMF.pure (CodeRelocation.frame (11 + (next n κ).length)
        (NativeCode.frame state trace { inputTape := input, outputTape := SimulatorPredecessorLookupExtract.targetMessage target suffix })) := by
    cases hc : (SimulatorLookup.tableBits table).map some with
    | nil => contradiction
    | cons head rest =>
        simpa only [startWith, hc, input, UnaryFuel.cursor] using UnaryFuel.empty_run (savedContext := savedContext) oracle state trace (next n κ) (failed n) used head rest (SimulatorPredecessorLookupExtract.targetMessage target suffix)
  rw [source_fuel_host] at hp
  have hpre := SimulatorPredecessorExtract.seq_run oracle (fuelPrefix initial) _ _ _ _ _ _ hp hf
  have hoff : (emptyPrefix initial κ).length = (fuelPrefix initial).length + (11 + (next n κ).length) := by
    simp [emptyPrefix, searchPrefix, CodeRelocation.code_length, UnaryFuel.body_length, Nat.add_assoc]
  have hpre' : TimedExecution.eval (Reification.timedStep (source initial κ) oracle) ((5 * k + 4) + (3 * used + 3))
      (NativeCode.frame state trace (start table 0 used target suffix)) =
      PMF.pure (CodeRelocation.frame (emptyPrefix initial κ).length
        (NativeCode.frame state trace { inputTape := input, outputTape := SimulatorPredecessorLookupExtract.targetMessage target suffix })) := by
    simpa only [source_fuel_host, hoff, CodeRelocation.frame, CodeRelocation.control,
      NativeCode.frame, Machine.Configuration.rebasePc, Nat.add_zero, Nat.add_assoc] using hpre
  rw [source_empty_host] at hpre'
  have h := SimulatorPredecessorExtract.seq_run oracle (emptyPrefix initial κ) (failed n) _ _ _ _ _ hpre'
    (failed_before oracle state trace target suffix input)
  let before : Machine.Configuration := { pc := (emptyPrefix initial κ).length + (n + 1), inputTape := input, outputTape := flagTape target suffix false }
  have hr : TimedExecution.eval (Reification.timedStep (source initial κ) oracle)
      (((5 * k + 4) + (3 * used + 3)) + (n + 1)) (NativeCode.frame state trace (start table 0 used target suffix)) =
      PMF.pure (NativeCode.frame state trace before) := by
    simpa only [source_empty_host, before, CodeRelocation.frame, CodeRelocation.control, NativeCode.frame, Machine.Configuration.rebasePc] using h
  have hh : (source initial κ)[before.pc]? = some (.native .halt) := by
    rw [source_empty_host, show before.pc = (emptyPrefix initial κ).length + (n + 1) from rfl, CodeRelocation.lookup, failed_halt]; rfl
  have hnpc : before.pc ≠ restartPc initial κ := by
    simp only [before, emptyPrefix, CodeRelocation.code_length, restart_offset]
    have hl : (next n κ).length = (SimulatorPredecessorLookupExtract.code n κ []).length + 5 := by
      rw [next_host, CodeRelocation.code_length]; rfl
    rw [hl]; omega
  have halts := retained_halt oracle state trace initial _ before _ rfl hr hh hnpc
  simpa only [before, input, show ((5 * k + 4) + (3 * used + 3) + (n + 1)) + 1 = (5 * k + 4) + (3 * used + 3) + (n + 2) by omega] using halts

theorem missing_layout (target : Bits n) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput : List (Option Bool)) (suffix : List (Bits κ))
    (hf : (MessagePrefixLoop.find target table).1 = none) :
    (SimulatorPredecessorLookup.finish target beforeInput [none]
      ((FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some) table).inputTape =
      { left := (table.flatMap SimulatorLookup.entryBits).reverse.map some ++ beforeInput, current := some false } ∧
    (SimulatorPredecessorLookup.finish target beforeInput [none]
      ((FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some) table).outputTape = flagTape target suffix false := by
  induction table generalizing beforeInput with
  | nil => constructor <;> rfl
  | cons entry rest ih =>
      by_cases hm : entry.1.2.1 = false ∧ entry.2 = target
      · simp [MessagePrefixLoop.find, hm] at hf
      · have ht : (MessagePrefixLoop.find target rest).1 = none := by
          simpa only [MessagePrefixLoop.find, hm, ↓reduceIte] using hf
        rw [SimulatorPredecessorLookup.finish, if_neg hm]
        have h := ih ((SimulatorLookup.entryBits entry).reverse.map some ++ beforeInput) ht
        simpa [List.flatMap_cons, List.reverse_append, List.map_append, List.append_assoc] using h

theorem missing_next_before (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (target : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat) (suffix : List (Bits κ))
    (_hf : (MessagePrefixLoop.find target table).1 = none) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host (next n κ) (failed n)) oracle)
      (SimulatorPredecessorLookup.steps target table - 1)
      (NativeCode.frame state trace (start table fuel used target suffix)) =
      PMF.pure (NativeCode.frame state trace
        { SimulatorPredecessorLookup.finish target (none :: UnaryFuel.counterWith savedContext fuel used)
          [none] ((FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some) table with halted := false }) := by
  have hp := SimulatorPredecessorLookup.before_halt oracle state trace target table
    (none :: UnaryFuel.counterWith savedContext fuel used) [none] ((FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some)
  have he := SelectiveHaltReturn.active_eval (SimulatorPredecessorLookup.code n κ)
    (SimulatorPredecessorLookup.code n κ).length (fun pc => pc == SimulatorPredecessorStep.foundPc n κ)
    oracle (SimulatorPredecessorLookup.steps target table - 1)
    (NativeCode.frame state trace (start table fuel used target suffix))
    (by intro out hm; change out ∈ (TimedExecution.eval _ _ (NativeCode.frame state trace (SimulatorPredecessorLookup.start table target _ _ _))).support at hm; rw [hp, PMF.mem_support_pure_iff] at hm; subst out; rfl)
  have ha := CodePrefixExecution.append_active (SimulatorPredecessorLookupExtract.lookupCode n κ)
    ((SimulatorPredecessorExtract.code n κ rewind).map (CodeRelocation.instruction (SimulatorPredecessorLookupExtract.lookupCode n κ).length) ++
      (failed n).map (CodeRelocation.instruction (next n κ).length)) oracle
    (SimulatorPredecessorLookup.steps target table - 1)
    (NativeCode.frame state trace (start table fuel used target suffix))
    (by intro out hm; change out ∈ (TimedExecution.eval (Reification.timedStep (SelectiveHaltReturn.code _ _ _) oracle) _ _).support at hm; rw [he] at hm; change out ∈ (TimedExecution.eval _ _ (NativeCode.frame state trace (SimulatorPredecessorLookup.start table target _ _ _))).support at hm; rw [hp, PMF.mem_support_pure_iff] at hm; subst out; rfl)
  have hform : CodeRelocation.host (next n κ) (failed n) = SimulatorPredecessorLookupExtract.lookupCode n κ ++
      ((SimulatorPredecessorExtract.code n κ rewind).map (CodeRelocation.instruction (SimulatorPredecessorLookupExtract.lookupCode n κ).length) ++
        (failed n).map (CodeRelocation.instruction (next n κ).length)) := by
    simp only [next, SimulatorPredecessorLookupExtract.code, CodeRelocation.host, List.append_assoc]
  rw [hform, ha]
  change TimedExecution.eval (Reification.timedStep (SelectiveHaltReturn.code _ _ _) oracle) _ _ = _
  rw [he]
  exact hp

theorem next_missing_halt : (CodeRelocation.host (next n κ) (failed n))[SimulatorPredecessorStep.missingPc n κ]? = some (.native .halt) := by
  have hh : (SimulatorPredecessorLookupExtract.lookupCode n κ)[SimulatorPredecessorStep.missingPc n κ]? = some (.native .halt) := by
    rw [SimulatorPredecessorLookupExtract.lookupCode, SelectiveHaltReturn.lookup,
      SimulatorPredecessorLookup.code, SelectiveHaltReturn.lookup, SimulatorPredecessorStep.missing_halt]
    have hn : SimulatorPredecessorStep.missingPc n κ ≠ SimulatorPredecessorStep.foundPc n κ := by
      obtain ⟨hf, _, _, hm⟩ := SimulatorPredecessorStep.pc_formulas n κ; omega
    simp [SelectiveHaltReturn.instruction, SimulatorPredecessorLookup.returns_missing, hn]
  have hi : SimulatorPredecessorStep.missingPc n κ < (SimulatorPredecessorLookupExtract.lookupCode n κ).length :=
    (List.getElem?_eq_some_iff.mp hh).1
  simp only [next, SimulatorPredecessorLookupExtract.code, CodeRelocation.host, List.append_assoc]
  rw [List.getElem?_append_left hi, hh]

theorem missing_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial target : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat) (suffix : List (Bits κ))
    (hn : target ≠ initial) (hf : (MessagePrefixLoop.find target table).1 = none) :
    ∃ k, k < n ∧
      TimedExecution.eval (Reification.timedStep (code initial κ) oracle)
        (((5 * k + 4) + (6 * used + 7)) + SimulatorPredecessorLookup.steps target table)
        (NativeCode.frame state trace (start table (fuel + 1) used target suffix)) =
        PMF.pure (NativeCode.frame state trace
          { pc := (searchPrefix initial κ).length + SimulatorPredecessorStep.missingPc n κ,
            inputTape := { left := (table.flatMap SimulatorLookup.entryBits).reverse.map some ++ none :: UnaryFuel.counterWith savedContext fuel (used + 1), current := some false },
            outputTape := flagTape target suffix false, halted := true }) := by
  obtain ⟨k, hk, hp⟩ := begin_search (savedContext := savedContext) oracle state trace initial target table fuel used suffix hn
  refine ⟨k, hk, ?_⟩
  have hs := missing_next_before (savedContext := savedContext) oracle state trace target table fuel (used + 1) suffix hf
  rw [source_search_host] at hp
  have h := SimulatorPredecessorExtract.seq_run oracle (searchPrefix initial κ) _ _ _ _ _ _ hp hs
  let before : Machine.Configuration := { pc := (searchPrefix initial κ).length + SimulatorPredecessorStep.missingPc n κ, inputTape := { left := (table.flatMap SimulatorLookup.entryBits).reverse.map some ++ none :: UnaryFuel.counterWith savedContext fuel (used + 1), current := some false }, outputTape := flagTape target suffix false }
  have hpc := SimulatorPredecessorLookupExtract.missing_cursor target table
    (none :: UnaryFuel.counterWith savedContext fuel (used + 1)) [none] ((FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some) hf
  have hl := missing_layout target table (none :: UnaryFuel.counterWith savedContext fuel (used + 1)) suffix hf
  have hframe : CodeRelocation.frame (searchPrefix initial κ).length
      (NativeCode.frame state trace { SimulatorPredecessorLookup.finish target (none :: UnaryFuel.counterWith savedContext fuel (used + 1))
        [none] ((FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some) table with halted := false }) = NativeCode.frame state trace before := by
    simp only [NativeCode.frame, CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc,
      before, hpc, hl.1, hl.2]
  rw [hframe, ← source_search_host] at h
  have hh : (source initial κ)[before.pc]? = some (.native .halt) := by
    rw [source_search_host, show before.pc = (searchPrefix initial κ).length + SimulatorPredecessorStep.missingPc n κ from rfl,
      CodeRelocation.lookup, next_missing_halt]; rfl
  have hne : before.pc ≠ restartPc initial κ := by
    rw [restart_offset]
    have hfpc := SimulatorPredecessorStep.pc_formulas n κ
    have hlen := SimulatorPredecessorLookupExtract.code_length n κ []
    simp only [List.length_nil, Nat.add_zero] at hlen
    dsimp only [before]; omega
  have hr := retained_halt oracle state trace initial _ before _ rfl h hh hne
  have hpos := SimulatorPredecessorLookup.steps_positive target table
  have htime : ((5 * k + 4) + (6 * used + 7) + (SimulatorPredecessorLookup.steps target table - 1)) + 1 =
      (5 * k + 4) + (6 * used + 7) + SimulatorPredecessorLookup.steps target table := by omega
  simpa only [htime, before] using hr

def tapeContent (tape : Tape) : List (Option Bool) := tape.left.reverse ++ tape.current :: tape.right
def retainsTable (table : CompressionTable (Bits κ) (Bits n)) (input : Tape) : Prop :=
  ∃ context, tapeContent input = context ++ (SimulatorLookup.tableBits table).map some

theorem frontier_content (left cells : List (Option Bool)) (hn : cells ≠ []) :
    tapeContent (FixedWidthCopy.frontier left cells) = left.reverse ++ cells := by
  cases cells <;> simp_all [tapeContent, FixedWidthCopy.frontier, ResponseLoading.fromCells]

theorem start_retains (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat)
    (target : Bits n) (suffix : List (Bits κ)) : retainsTable table (start table fuel used target suffix).inputTape := by
  refine ⟨(none :: UnaryFuel.counterWith savedContext fuel used).reverse, ?_⟩
  exact frontier_content _ _ (by simpa using table_nonempty table)

def Represents (table : CompressionTable (Bits κ) (Bits n)) (message : Option (List (Bits κ)))
    (machine : Machine.Configuration) : Prop :=
  machine.halted = true ∧ machine.outputTape.current = some message.isSome ∧
    (∀ blocks, message = some blocks → machine.outputTape.right = (FiniteBitEncoding.encodeList (fixedBits κ) blocks).map some) ∧
    retainsTable table machine.inputTape ∧
    ∃ remaining, tapeContent machine.inputTape = savedContext.reverse ++ remaining

local notation "Represents" => SimulatorReconstruct.Represents (savedContext := savedContext)

theorem start_protects (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat)
    (target : Bits n) (suffix : List (Bits κ)) :
    ∃ remaining, tapeContent (start table fuel used target suffix).inputTape = savedContext.reverse ++ remaining := by
  refine ⟨(none :: UnaryFuel.counter fuel used).reverse ++ (SimulatorLookup.tableBits table).map some, ?_⟩
  change tapeContent (FixedWidthCopy.frontier (none :: UnaryFuel.counterWith savedContext fuel used) _) = _
  rw [frontier_content _ _ (by simpa using table_nonempty table), UnaryFuel.counterWith_eq_append]
  simp [List.reverse_append, List.reverse_cons, List.append_assoc]

def roundBound (table : CompressionTable (Bits κ) (Bits n)) (cap : Nat) : Nat :=
  table.length * (17 * n + 8 * κ + 26) + 20 * n + 10 * κ + 50 + 6 * cap
def budget (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat) : Nat :=
  (fuel + 1) * roundBound table (fuel + used)

theorem round_le_budget (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat) :
    roundBound table (fuel + used) ≤ budget table fuel used := by
  unfold budget
  nlinarith

theorem table_payload_length (table : CompressionTable (Bits κ) (Bits n)) :
    (table.flatMap SimulatorLookup.entryBits).length = table.length * (3 * n + 2 * κ + 4) := by
  have hentry (entry : CompressionInput (Bits κ) (Bits n) × Bits n) :
      (SimulatorLookup.entryBits entry).length = 3 * n + 2 * κ + 4 := by
    simp [SimulatorLookup.entryBits, FiniteBitEncoding.delimit_length, compressionPacket]
    omega
  induction table with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.flatMap_cons, List.length_append, hentry, ih, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem cycle_bound (table before after : CompressionTable (Bits κ) (Bits n))
    (target previous : Bits n) (block : Bits κ) (k used fuel : Nat)
    (hk : k < n) (ht : table = before ++ ((previous, (false, block)), target) :: after) :
    (((5 * k + 4) + (6 * used + 7)) +
      (SimulatorPredecessorLookup.steps target table + (7 * n + 10 * κ + 13) +
        (3 * (before.flatMap SimulatorLookup.entryBits).length + 5)) + 1) ≤
      roundBound table (fuel + 1 + used) := by
  have hs := SimulatorPredecessorLookup.steps_bound target table
  have hl : before.length ≤ table.length := by rw [ht]; simp
  have hp := Nat.mul_le_mul_right (3 * n + 2 * κ + 4) hl
  rw [← table_payload_length before] at hp
  unfold roundBound
  nlinarith

theorem accepted_represents (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat)
    (initial : Bits n) (suffix : List (Bits κ)) :
    Represents table (some suffix)
      { pc := 2 * n + 1, inputTape := (start table fuel used initial suffix).inputTape,
        outputTape := flagTape initial suffix true, halted := true } := by
  refine ⟨rfl, rfl, ?_, start_retains table fuel used initial suffix, start_protects table fuel used initial suffix⟩
  intro blocks he; cases Option.some.inj he; rfl

theorem empty_represents (table : CompressionTable (Bits κ) (Bits n)) (used : Nat)
    (target : Bits n) (suffix : List (Bits κ)) (pc : Nat) :
    Represents table none
      { pc := pc, inputTape := { left := savedContext, current := none, right := List.replicate used (some false) ++ none :: (SimulatorLookup.tableBits table).map some },
        outputTape := flagTape target suffix false, halted := true } := by
  refine ⟨rfl, rfl, (by intro blocks he; cases he), ?_, ?_⟩
  · refine ⟨savedContext.reverse ++ none :: List.replicate used (some false) ++ [none], ?_⟩
    simp [tapeContent, List.append_assoc]
  · exact ⟨_, rfl⟩

theorem missing_represents (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat)
    (target : Bits n) (suffix : List (Bits κ)) (pc : Nat) :
    Represents table none
      { pc := pc, inputTape := { left := (table.flatMap SimulatorLookup.entryBits).reverse.map some ++ none :: UnaryFuel.counterWith savedContext fuel used, current := some false },
        outputTape := flagTape target suffix false, halted := true } := by
  refine ⟨rfl, rfl, (by intro blocks he; cases he), ?_, ?_⟩
  · refine ⟨(UnaryFuel.counterWith savedContext fuel used).reverse ++ [none], ?_⟩
    simp [tapeContent, SimulatorLookup.tableBits, List.reverse_append, ← List.map_reverse,
      List.map_append, List.append_assoc]
  · refine ⟨(UnaryFuel.counter fuel used).reverse ++ [none] ++ (SimulatorLookup.tableBits table).map some, ?_⟩
    simp [tapeContent, SimulatorLookup.tableBits, UnaryFuel.counterWith_eq_append, List.reverse_append,
      ← List.map_reverse, List.map_append, List.append_assoc]

/-- Exact bounded simulation of the reference reconstruction on every finite
table, including cycles, collisions, zero-width digests and empty messages.
External state and all old history are retained in the returned physical frame. -/
theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat) (target : Bits n) (suffix : List (Bits κ)) :
    ∃ time result, time ≤ budget table fuel used ∧
      TimedExecution.eval (Reification.timedStep (code initial κ) oracle) time
        (NativeCode.frame state trace (start table fuel used target suffix)) = PMF.pure (NativeCode.frame state trace result) ∧
      Represents table (MessagePrefixLoop.run initial table fuel target suffix).message result := by
  induction fuel generalizing used target suffix with
  | zero =>
      by_cases ht : target = initial
      · subst target
        refine ⟨2 * n + 2, _, ?_, accepted_run oracle state trace initial table 0 used suffix, ?_⟩
        · have hb := round_le_budget table 0 used
          unfold roundBound at hb; omega
        · simpa only [MessagePrefixLoop.run, ↓reduceIte] using accepted_represents table 0 used initial suffix
      · obtain ⟨k, hk, hr⟩ := empty_run (savedContext := savedContext) oracle state trace initial target table used suffix ht
        refine ⟨_, _, ?_, hr, ?_⟩
        · have hb := round_le_budget table 0 used
          unfold roundBound at hb; omega
        · simpa only [MessagePrefixLoop.run, if_neg ht] using empty_represents table used target suffix ((emptyPrefix initial κ).length + (n + 1))
  | succ fuel ih =>
      by_cases ht : target = initial
      · subst target
        refine ⟨2 * n + 2, _, ?_, accepted_run oracle state trace initial table (fuel + 1) used suffix, ?_⟩
        · have hb := round_le_budget table (fuel + 1) used
          unfold roundBound at hb; omega
        · simpa only [MessagePrefixLoop.run, ↓reduceIte] using accepted_represents table (fuel + 1) used initial suffix
      · cases hf : (MessagePrefixLoop.find target table).1 with
        | none =>
            obtain ⟨k, hk, hr⟩ := missing_run (savedContext := savedContext) oracle state trace initial target table fuel used suffix ht hf
            refine ⟨_, _, ?_, hr, ?_⟩
            · have hb := round_le_budget table (fuel + 1) used
              have hs := SimulatorPredecessorLookup.steps_bound target table
              unfold roundBound at hb
              nlinarith
            · simpa only [MessagePrefixLoop.run, if_neg ht, hf] using
                missing_represents table fuel (used + 1) target suffix ((searchPrefix initial κ).length + SimulatorPredecessorStep.missingPc n κ)
        | some pair =>
            rcases pair with ⟨previous, block⟩
            obtain ⟨k, before, after, hk, htable, hcycle⟩ := cycle_run (savedContext := savedContext) oracle state trace initial target previous block table fuel used suffix ht hf
            obtain ⟨time, result, hb, hr, hout⟩ := ih (used + 1) previous (block :: suffix)
            refine ⟨(((5 * k + 4) + (6 * used + 7)) + (SimulatorPredecessorLookup.steps target table + (7 * n + 10 * κ + 13) + (3 * (before.flatMap SimulatorLookup.entryBits).length + 5)) + 1) + time, result, ?_, ?_, ?_⟩
            · have hc := cycle_bound table before after target previous block k used fuel hk htable
              have hcap : fuel + (used + 1) = fuel + 1 + used := by omega
              simp only [budget, hcap, Nat.add_mul, Nat.one_mul] at hb ⊢
              omega
            · rw [TimedExecution.eval_add, hcycle, PMF.pure_bind, hr]
            · simpa only [MessagePrefixLoop.run, if_neg ht, hf] using hout

/-- A common public horizon, with true stopping rather than host-side restart. -/
theorem run_at_budget (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (fuel used : Nat) (target : Bits n) (suffix : List (Bits κ)) :
    ∃ result,
      TimedExecution.eval (Reification.timedStep (code initial κ) oracle) (budget table fuel used)
        (NativeCode.frame state trace (start table fuel used target suffix)) = PMF.pure (NativeCode.frame state trace result) ∧
      Represents table (MessagePrefixLoop.run initial table fuel target suffix).message result := by
  obtain ⟨time, result, hb, hr, hout⟩ := run (savedContext := savedContext) oracle state trace initial table fuel used target suffix
  refine ⟨result, ?_, hout⟩
  have ha : Reification.timedStep (code initial κ) oracle (NativeCode.frame state trace result) =
      PMF.pure (NativeCode.frame state trace result) := by
    simp [Reification.timedStep, Reification.terminal, NativeCode.frame, hout.1]
  rw [show budget table fuel used = time + (budget table fuel used - time) from by omega,
    TimedExecution.eval_add, hr, PMF.pure_bind, TimedExecution.Block.eval_of_absorbing _ ha]

def readResult (κ : Nat) (machine : Machine.Configuration) : Option (List (Bits κ)) :=
  if machine.outputTape.current = some true then
    (FiniteBitEncoding.list (fixedBits κ)).decode (machine.outputTape.right.filterMap id)
  else none

theorem read_represents (table : CompressionTable (Bits κ) (Bits n)) (message : Option (List (Bits κ)))
    (machine : Machine.Configuration) (h : Represents table message machine) : readResult κ machine = message := by
  rcases h with ⟨_, hflag, hmessage, _⟩
  cases message with
  | none => simp [readResult, hflag]
  | some blocks =>
      rw [readResult, hflag]
      simp only [Option.isSome_some, ↓reduceIte]
      rw [hmessage blocks rfl]
      have hf : ((FiniteBitEncoding.encodeList (fixedBits κ) blocks).map some).filterMap id =
          FiniteBitEncoding.encodeList (fixedBits κ) blocks := by
        simp [List.filterMap_map]
      rw [hf]
      exact (FiniteBitEncoding.list (fixedBits κ)).decode_encode blocks

/-- Machine reconstruction refines the original messagePrefix, not just the
one-step reference loop. Empty messages and cyclic tables are included. -/
theorem reconstruct_eq (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial target : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (fuel : Nat) :
    ∃ result,
      TimedExecution.eval (Reification.timedStep (code initial κ) oracle) (budget table fuel 0)
        (NativeCode.frame state trace (start table fuel 0 target [])) = PMF.pure (NativeCode.frame state trace result) ∧
      readResult κ result = messagePrefix initial table fuel target ∧ result.halted = true ∧
      retainsTable table result.inputTape := by
  obtain ⟨result, hr, hout⟩ := run_at_budget (savedContext := savedContext) oracle state trace initial table fuel 0 target []
  refine ⟨result, hr, ?_, hout.1, hout.2.2.2.1⟩
  rw [read_represents _ _ _ hout, MessagePrefixLoop.run_eq]
  simp

/-- Complete encoded storage, including unary fuel, physical table, growing
suffix, emitted code, opaque external state, and every old trace entry. -/
theorem encoded_peak (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (initial target : Bits n) (table : CompressionTable (Bits κ) (Bits n))
    (fuel used : Nat) (suffix : List (Bits κ)) (elapsed : Nat)
    (within : elapsed ≤ budget table fuel used) (out : Configuration State)
    (supported : out ∈ (TimedExecution.eval (Reification.timedStep (code initial κ) oracle) elapsed
      (NativeCode.frame state trace (start table fuel used target suffix))).support) :
    ((NativeCode.fullEncoding E).encode (code initial κ, out)).length ≤
      NativeCode.storageBound (code initial κ)
        (NativePacketComponent.Resources.frameSize stateSize (NativeCode.frame state trace (start table fuel used target suffix)))
        (budget table fuel used) :=
  NativeCode.encoded_peak E stateSize hState oracle state trace _ (code_native _ _) _ _ elapsed within out supported

theorem encoded_finish (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (initial target : Bits n) (table : CompressionTable (Bits κ) (Bits n))
    (fuel used : Nat) (suffix : List (Bits κ)) :
    ∃ result,
      TimedExecution.eval (Reification.timedStep (code initial κ) oracle) (budget table fuel used)
        (NativeCode.frame state trace (start table fuel used target suffix)) = PMF.pure (NativeCode.frame state trace result) ∧
      Represents table (MessagePrefixLoop.run initial table fuel target suffix).message result ∧
      ((NativeCode.fullEncoding E).encode (code initial κ, NativeCode.frame state trace result)).length ≤
        NativeCode.storageBound (code initial κ)
          (NativePacketComponent.Resources.frameSize stateSize (NativeCode.frame state trace (start table fuel used target suffix)))
          (budget table fuel used) := by
  obtain ⟨result, hr, hout⟩ := run_at_budget (savedContext := savedContext) oracle state trace initial table fuel used target suffix
  refine ⟨result, hr, hout, ?_⟩
  exact encoded_peak E stateSize hState oracle state trace initial target table fuel used suffix _ (Nat.le_refl _) _
    (by rw [hr]; simp)

structure Input (n κ : Nat) where
  table : CompressionTable (Bits κ) (Bits n)
  fuel : Nat
  used : Nat := 0
  target : Bits n
  suffix : List (Bits κ) := []

noncomputable def finish (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial : Bits n) (input : Input n κ) : Machine.Configuration :=
  Classical.choose (run_at_budget (savedContext := savedContext) oracle state trace initial input.table input.fuel input.used input.target input.suffix)

theorem finish_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial : Bits n) (input : Input n κ) :
    TimedExecution.eval (Reification.timedStep (code initial κ) oracle) (budget input.table input.fuel input.used)
      (NativeCode.frame state trace (start input.table input.fuel input.used input.target input.suffix)) =
      PMF.pure (NativeCode.frame state trace (finish (savedContext := savedContext) oracle state trace initial input)) :=
  (Classical.choose_spec (run_at_budget (savedContext := savedContext) oracle state trace initial input.table input.fuel input.used input.target input.suffix)).1

theorem finish_represents (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial : Bits n) (input : Input n κ) :
    Represents input.table (MessagePrefixLoop.run initial input.table input.fuel input.target input.suffix).message
      (finish (savedContext := savedContext) oracle state trace initial input) :=
  (Classical.choose_spec (run_at_budget (savedContext := savedContext) oracle state trace initial input.table input.fuel input.used input.target input.suffix)).2

/-- A full-state execution contract for the emitted fixed code. The selected
endpoint is certified by its execution, not populated from a reference answer. -/
noncomputable def procedure (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial : Bits n) :
    TimedExecution.Procedure (Reification.timedStep (code initial κ) oracle) (Input n κ) Machine.Configuration :=
  TimedExecution.Procedure.ofFixed _
    (fun (input : Input n κ) => NativeCode.frame state trace (start input.table input.fuel input.used input.target input.suffix))
    (fun _ (result : Machine.Configuration) => NativeCode.frame state trace result)
    (fun (input : Input n κ) => PMF.pure (finish (savedContext := savedContext) oracle state trace initial input))
    (fun (input : Input n κ) => budget input.table input.fuel input.used)
    (fun input => by simpa only [PMF.pure_map] using finish_run (savedContext := savedContext) oracle state trace initial input)

theorem procedure_costed (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial : Bits n) (input : Input n κ) :
    (procedure (savedContext := savedContext) oracle state trace initial).costed input =
      PMF.pure (finish (savedContext := savedContext) oracle state trace initial input, budget input.table input.fuel input.used) := by
  simp [procedure, TimedExecution.Procedure.ofFixed, PMF.pure_map]

def observe (κ : Nat) (frame : Configuration State) : Option (List (Bits κ)) :=
  match frame.control with
  | .running machine => readResult κ machine
  | _ => none

theorem message_law (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial target : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) (fuel : Nat) :
    (TimedExecution.eval (Reification.timedStep (code initial κ) oracle) (budget table fuel 0)
      (NativeCode.frame state trace (start table fuel 0 target []))).map (observe κ) =
      PMF.pure (messagePrefix initial table fuel target) := by
  obtain ⟨result, hr, hread, _, _⟩ := reconstruct_eq (savedContext := savedContext) oracle state trace initial target table fuel
  rw [hr, PMF.pure_map]
  simpa only [observe, NativeCode.frame] using congrArg PMF.pure hread

end SavedContext
end Foundation.Hash.Native.SimulatorReconstruct
