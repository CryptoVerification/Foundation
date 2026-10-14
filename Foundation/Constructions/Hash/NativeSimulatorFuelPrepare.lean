import Foundation.Constructions.Hash.NativeSimulatorTableCount
import Foundation.Crypto.Semantics.Oracle.NativeCodeTapeEquivalence

/-! Runtime preparation of the reconstruction fuel field. The original query
is kept in full on the output tape. Counter allocation, transfer, clearing, and
both table/counter scans are actual native instructions with exact costs. -/
namespace Foundation.Hash.Native.SimulatorFuelPrepare
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n κ : Nat}

def transferPrelude : Code := StraightLine.code [.left .input, .left .input, .right .output]
def finishCode (tail : Code) : Code :=
  CodeRelocation.host [.native (.moveRight .input)]
    (RightBlankSeek.code .input (CodeRelocation.host [.native (.moveRight .output)] tail))
def code (n κ : Nat) (tail : Code) : Code :=
  SimulatorTableCount.code n κ
    (LeftBlankRewind.code .input
      (CodeRelocation.host transferPrelude (UnaryCounterTransfer.code (finishCode tail))))

theorem finishCode_length (tail : Code) : (finishCode tail).length = 6 + tail.length := by
  simp [finishCode, RightBlankSeek.code, CodeRelocation.code_length, RightBlankSeek.body_length]
  omega

def start (table : CompressionTable (Bits κ) (Bits n)) (query : List (Option Bool)) : Machine.Configuration :=
  { inputTape := FixedWidthCopy.frontier [none] ((SimulatorLookup.tableBits table).map some), outputTape := { right := none :: query } }
def counted (table : CompressionTable (Bits κ) (Bits n)) (query : List (Option Bool)) : Machine.Configuration :=
  { inputTape := { left := (table.flatMap SimulatorLookup.entryBits).reverse.map some ++ [none], current := some false },
    outputTape := { right := List.replicate table.length (some true) ++ none :: query } }
def rewound (table : CompressionTable (Bits κ) (Bits n)) (query : List (Option Bool)) : Machine.Configuration :=
  { inputTape := FixedWidthCopy.frontier [none] ((SimulatorLookup.tableBits table).map some), outputTape := (counted table query).outputTape }
def copying (table : CompressionTable (Bits κ) (Bits n)) (query : List (Option Bool)) : Machine.Configuration :=
  { inputTape := { right := none :: (SimulatorLookup.tableBits table).map some },
    outputTape := FixedWidthCopy.frontier [none] (List.replicate table.length (some true) ++ none :: query) }
def copied (table : CompressionTable (Bits κ) (Bits n)) (query : List (Option Bool)) : Machine.Configuration :=
  { inputTape := { right := List.replicate table.length (some true) ++ none :: (SimulatorLookup.tableBits table).map some },
    outputTape := { left := List.replicate table.length none ++ [none], right := query } }
def finish (table : CompressionTable (Bits κ) (Bits n)) (query : List (Option Bool)) : Machine.Configuration :=
  { inputTape := UnaryFuel.tape table.length 0 ((SimulatorLookup.tableBits table).map some),
    outputTape := FixedWidthCopy.frontier (List.replicate (table.length + 2) none) query }

theorem code_length (n κ : Nat) (tail : Code) :
    (code n κ tail).length = 3 * n + 2 * κ + 27 + tail.length := by
  simp [code, SimulatorTableCount.code, SimulatorTableCount.body_length, SimulatorTableCount.width,
    LeftBlankRewind.code, LeftBlankRewind.body_length, transferPrelude, StraightLine.code,
    UnaryCounterTransfer.code, UnaryCounterTransfer.body, finishCode, RightBlankSeek.code,
    RightBlankSeek.body, CodeRelocation.code_length]
  omega

theorem rewind_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code)
    (table : CompressionTable (Bits κ) (Bits n)) (query : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (LeftBlankRewind.code .input tail) oracle)
      (3 * (table.flatMap SimulatorLookup.entryBits).length + 5)
      (NativeCode.frame state trace (counted table query)) =
      PMF.pure (CodeRelocation.frame 4 (NativeCode.frame state trace (rewound table query))) := by
  have h := LeftBlankRewind.run oracle state trace .input tail
    (false :: (table.flatMap SimulatorLookup.entryBits).reverse) [] [] (counted table query).outputTape
  simpa [counted, rewound, LeftBlankRewind.put, FixedWidthCopy.backwardFrontier,
    SimulatorLookup.tableBits, List.reverse_cons, List.map_append, List.append_assoc, Nat.mul_add,
    show 3 * ((table.flatMap SimulatorLookup.entryBits).length + 1) + 2 =
      3 * (table.flatMap SimulatorLookup.entryBits).length + 5 by omega] using h

theorem transfer_prepare (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code)
    (table : CompressionTable (Bits κ) (Bits n)) (query : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host transferPrelude tail) oracle) 3
      (NativeCode.frame state trace (rewound table query)) =
      PMF.pure (CodeRelocation.frame 3 (NativeCode.frame state trace (copying table query))) := by
  have h := StraightLine.public_run oracle state trace []
    (tail.map (CodeRelocation.instruction 3)) [.left .input, .left .input, .right .output]
    (rewound table query) rfl rfl
  have hn := SimulatorReconstruct.table_nonempty table
  generalize hc : (SimulatorLookup.tableBits table).map some = cells at *
  have hne : cells ≠ [] := by simpa [← hc] using hn
  cases cells with
  | nil => contradiction
  | cons head rest =>
      cases hlen : table.length <;>
      simpa [transferPrelude, StraightLine.code, rewound, counted, copying, hc, hlen, CodeRelocation.host,
        CodeRelocation.frame, CodeRelocation.control, NativeCode.frame, Machine.Configuration.rebasePc,
        StraightLine.execute, StraightLine.apply, Machine.Configuration.updateTape,
        Machine.Configuration.advance, FixedWidthCopy.frontier, ResponseLoading.fromCells,
        Tape.moveLeft, Tape.moveRight, List.replicate_succ] using h

theorem transfer_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code)
    (table : CompressionTable (Bits κ) (Bits n)) (query : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (UnaryCounterTransfer.code tail) oracle) (6 * table.length + 1)
      (NativeCode.frame state trace (copying table query)) =
      PMF.pure (CodeRelocation.frame 6 (NativeCode.frame state trace (copied table query))) :=
  UnaryCounterTransfer.run oracle state trace tail table.length
    (none :: (SimulatorLookup.tableBits table).map some) [none] query

theorem finish_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code)
    (table : CompressionTable (Bits κ) (Bits n)) (query : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (finishCode tail) oracle) (3 * table.length + 4)
      (NativeCode.frame state trace (copied table query)) =
      PMF.pure (CodeRelocation.frame 6 (NativeCode.frame state trace (finish table query))) := by
  have hp : TimedExecution.eval (Reification.timedStep (finishCode tail) oracle) 1
      (NativeCode.frame state trace (copied table query)) =
      PMF.pure (CodeRelocation.frame 1 (NativeCode.frame state trace
        { inputTape := FixedWidthCopy.frontier [none] (List.replicate table.length (some true) ++ none :: (SimulatorLookup.tableBits table).map some),
          outputTape := (copied table query).outputTape })) := by
    cases ht : table.length <;>
      simp [finishCode, CodeRelocation.host, copied, ht, TimedExecution.eval,
        Reification.timedStep, Reification.terminal, NativeCode.frame, Reification.perform,
        Reification.action, transition, Machine.Instruction.next, Machine.Configuration.advance,
        Machine.Configuration.updateTape, Tape.moveRight, FixedWidthCopy.frontier, ResponseLoading.fromCells,
        List.replicate_succ, CodeRelocation.frame, CodeRelocation.control, Machine.Configuration.rebasePc]
  have hs := RightBlankSeek.run oracle state trace .input (CodeRelocation.host [.native (.moveRight .output)] tail)
    (List.replicate table.length true) [none] ((SimulatorLookup.tableBits table).map some) (copied table query).outputTape
  simp only [List.length_replicate, List.map_replicate, List.reverse_replicate, LeftBlankRewind.put] at hs
  let ready : Machine.Configuration := { inputTape := FixedWidthCopy.frontier (none :: List.replicate table.length (some true) ++ [none]) ((SimulatorLookup.tableBits table).map some), outputTape := (copied table query).outputTape }
  have hm : TimedExecution.eval (Reification.timedStep (CodeRelocation.host [.native (.moveRight .output)] tail) oracle) 1
      (NativeCode.frame state trace ready) = PMF.pure (CodeRelocation.frame 1 (NativeCode.frame state trace (finish table query))) := by
    cases query <;>
      simp [CodeRelocation.host, copied, ready, finish, UnaryFuel.tape, UnaryFuel.counter,
        TimedExecution.eval, Reification.timedStep, Reification.terminal, NativeCode.frame,
        Reification.perform, Reification.action, transition, Machine.Instruction.next,
        Machine.Configuration.advance, Machine.Configuration.updateTape, Tape.moveRight,
        FixedWidthCopy.frontier, ResponseLoading.fromCells, CodeRelocation.frame, CodeRelocation.control,
        Machine.Configuration.rebasePc, List.replicate_succ, UnaryFuel.replicate_push]
  have hbody := SimulatorPredecessorExtract.seq_run oracle (RightBlankSeek.body .input)
    (CodeRelocation.host [.native (.moveRight .output)] tail) _ _ _ _ _ hs hm
  have h := SimulatorPredecessorExtract.seq_run oracle [.native (.moveRight .input)] _ _ _ _ _ _ hp hbody
  have ht : 1 + (3 * table.length + 2 + 1) = 3 * table.length + 4 := by omega
  simpa [ht, finishCode, RightBlankSeek.code, CodeRelocation.frame, CodeRelocation.control,
    NativeCode.frame, Machine.Configuration.rebasePc, RightBlankSeek.body_length, finish] using h

theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code)
    (table : CompressionTable (Bits κ) (Bits n)) (query : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ tail) oracle)
      (table.length * (4 * SimulatorTableCount.width n κ + 13) + 14)
      (NativeCode.frame state trace (start table query)) =
      PMF.pure (CodeRelocation.frame (code n κ []).length (NativeCode.frame state trace (finish table query))) := by
  have hf := finish_run oracle state trace tail table query
  have ht := SimulatorPredecessorExtract.seq_run oracle UnaryCounterTransfer.body _ _ _ _ _ _
    (transfer_run oracle state trace (finishCode tail) table query) hf
  have hp := SimulatorPredecessorExtract.seq_run oracle transferPrelude _ _ _ _ _ _
    (transfer_prepare oracle state trace (UnaryCounterTransfer.code (finishCode tail)) table query) ht
  have hr := SimulatorPredecessorExtract.seq_run oracle (LeftBlankRewind.body .input) _ _ _ _ _ _
    (rewind_run oracle state trace (CodeRelocation.host transferPrelude (UnaryCounterTransfer.code (finishCode tail))) table query) hp
  have hc := SimulatorTableCount.run oracle state trace
    (LeftBlankRewind.code .input (CodeRelocation.host transferPrelude (UnaryCounterTransfer.code (finishCode tail)))) table [none] (none :: query)
  have h := SimulatorPredecessorExtract.seq_run oracle (SimulatorTableCount.body n κ) _ _ _ _ _ _ hc hr
  have hsize := SimulatorReconstruct.table_payload_length table
  have htime : table.length * (SimulatorTableCount.width n κ + 4) + 1 +
      (3 * (table.flatMap SimulatorLookup.entryBits).length + 5 + (3 + (6 * table.length + 1 + (3 * table.length + 4)))) =
      table.length * (4 * SimulatorTableCount.width n κ + 13) + 14 := by
    rw [hsize]; unfold SimulatorTableCount.width; ring
  rw [htime] at h
  simpa only [code, SimulatorTableCount.code, LeftBlankRewind.code, UnaryCounterTransfer.code,
    CodeRelocation.frame, CodeRelocation.control, NativeCode.frame, Machine.Configuration.rebasePc,
    CodeRelocation.code_length, finishCode_length, List.length_nil, start, Nat.add_zero, Nat.add_assoc] using h

theorem link (n κ : Nat) (tail : Code) : code n κ tail = CodeRelocation.host (code n κ []) tail := by
  simp only [code, SimulatorTableCount.code, LeftBlankRewind.code, UnaryCounterTransfer.code,
    finishCode, RightBlankSeek.code, ← CodeRelocation.host_assoc]
  simp [CodeRelocation.host]

theorem code_native (n κ : Nat) (tail : Code)
    (ht : ∀ op ∈ tail, ∃ native, op = .native native) :
    ∀ op ∈ code n κ tail, ∃ native, op = .native native := by
  apply CodeRelocation.host_native
  · exact SimulatorTableCount.body_native _ _
  apply CodeRelocation.host_native
  · exact LeftBlankRewind.body_native _
  apply CodeRelocation.host_native
  · intro op hm; obtain ⟨action, _, rfl⟩ := List.mem_map.mp hm; exact ⟨_, rfl⟩
  apply CodeRelocation.host_native
  · exact UnaryCounterTransfer.body_native
  apply CodeRelocation.host_native
  · intro op hm; exact ⟨_, by simpa using hm⟩
  apply CodeRelocation.host_native
  · exact RightBlankSeek.body_native _
  exact CodeRelocation.host_native _ _ (by intro op hm; exact ⟨_, by simpa using hm⟩) ht

theorem blank_frontier_equivalent (blanks : Nat) (cells : List (Option Bool)) :
    (FixedWidthCopy.frontier (List.replicate blanks none) cells).Equivalent (FixedWidthCopy.frontier [none] cells) := by
  refine ⟨rfl, ?_, fun _ => rfl⟩
  intro i
  change (List.replicate blanks (none : Option Bool)).getD i none = [none].getD i none
  have h₁ := (Tape.blank_padding_equivalent [] blanks).2.2 i
  have h₂ := (Tape.blank_padding_equivalent [] 1).2.2 i
  exact h₁.trans h₂.symm

theorem finish_equivalent (table : CompressionTable (Bits κ) (Bits n)) (target : Bits n)
    (suffix : List (Bits κ)) :
    (finish table (target.toList.map some ++ none :: (FiniteBitEncoding.encodeList (fixedBits κ) suffix).map some)).Equivalent
      (SimulatorReconstruct.start table table.length 0 target suffix) :=
  ⟨rfl, rfl, Tape.Equivalent.refl _, blank_frontier_equivalent _ _⟩

theorem observe_equivalent {State : Type*} (κ : Nat) (first second : Configuration State)
    (h : NativeCode.CellEquivalent first second) : SimulatorReconstruct.observe κ first = SimulatorReconstruct.observe κ second := by
  cases h with
  | finished => rfl
  | running state trace first second he =>
      have hr : ({ right := first.outputTape.right } : Tape).Equivalent { right := second.outputTape.right } :=
        ⟨rfl, fun _ => rfl, he.2.2.2.2.2⟩
      have hf := hr.bits
      simp [Tape.bits] at hf
      change first.outputTape.right.filterMap id = second.outputTape.right.filterMap id at hf
      simp only [SimulatorReconstruct.observe, NativeCode.frame, SimulatorReconstruct.readResult,
        he.2.2.2.1, hf]

/-- Once the caller has saved the key and supplied target/encoded suffix cells,
fuel is created by the real table scan rather than assumed at loop entry. Extra
outer blanks execute the same native code; no normalization is performed. -/
theorem with_reconstruct_law (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial target : Bits n)
    (table : CompressionTable (Bits κ) (Bits n)) :
    (TimedExecution.eval (Reification.timedStep (code n κ (SimulatorReconstruct.code initial κ)) oracle)
      ((table.length * (4 * SimulatorTableCount.width n κ + 13) + 14) + SimulatorReconstruct.budget table table.length 0)
      (NativeCode.frame state trace (start table (target.toList.map some ++ [none, some false])))).map (SimulatorReconstruct.observe κ) =
      PMF.pure (messagePrefix initial table table.length target) := by
  have hp := run oracle state trace (SimulatorReconstruct.code initial κ) table (target.toList.map some ++ [none, some false])
  have he := finish_equivalent table target ([] : List (Bits κ))
  simp only [FiniteBitEncoding.encodeList, List.map_cons, List.map_nil] at he
  have eq := NativeCode.eval_map_eq_of_cellEquivalent (SimulatorReconstruct.code initial κ)
    (SimulatorReconstruct.code_native _ _) oracle (SimulatorReconstruct.budget table table.length 0)
    (NativeCode.frame state trace (finish table (target.toList.map some ++ [none, some false])))
    (NativeCode.frame state trace (SimulatorReconstruct.start table table.length 0 target []))
    (.running state trace _ _ he) (SimulatorReconstruct.observe κ) (observe_equivalent κ)
  rw [TimedExecution.eval_add, hp, PMF.pure_bind, link, CodeRelocation.eval, PMF.map_comp]
  have hf : (SimulatorReconstruct.observe κ ∘ CodeRelocation.frame (code n κ []).length) = SimulatorReconstruct.observe (State := State) κ := by
    funext frame
    cases hc : frame.control <;>
      simp [SimulatorReconstruct.observe, CodeRelocation.frame, CodeRelocation.control,
        hc, SimulatorReconstruct.readResult, Machine.Configuration.rebasePc]
  rw [hf, eq, SimulatorReconstruct.message_law]

def steps (table : CompressionTable (Bits κ) (Bits n)) : Nat :=
  table.length * (4 * SimulatorTableCount.width n κ + 13) + 14

theorem encoded_peak (E : FiniteBitEncoding State) (stateSize : State → Nat)
    (hState : ∀ state, (E.encode state).length ≤ stateSize state)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (table : CompressionTable (Bits κ) (Bits n)) (query : List (Option Bool)) (elapsed : Nat)
    (within : elapsed ≤ steps table) (out : Configuration State)
    (supported : out ∈ (TimedExecution.eval (Reification.timedStep (code n κ []) oracle) elapsed
      (NativeCode.frame state trace (start table query))).support) :
    ((NativeCode.fullEncoding E).encode (code n κ [], out)).length ≤
      NativeCode.storageBound (code n κ [])
        (NativePacketComponent.Resources.frameSize stateSize (NativeCode.frame state trace (start table query))) (steps table) :=
  NativeCode.encoded_peak E stateSize hState oracle state trace _ (code_native _ _ _ (by simp)) _ _ elapsed within out supported

end Foundation.Hash.Native.SimulatorFuelPrepare
