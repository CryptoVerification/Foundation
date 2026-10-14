import Foundation.Constructions.Hash.NativeSimulatorTerminalFuel
import Foundation.Crypto.Semantics.Oracle.LeftBlankAllocate
import Foundation.Crypto.Semantics.Oracle.FieldOverwrite

/-! Copy the original runtime packet beyond the fuel's left blank boundary,
then overwrite the old terminal field with an empty message suffix. Allocation,
copying, erasure, and restoration are real native actions. -/
namespace Foundation.Hash.Native.SimulatorKeyProtect
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n κ : Nat}

def savedContext (query : CompressionInput (Bits κ) (Bits n)) : List (Option Bool) :=
  (compressionPacket query).reverse.map some ++ [none]
def width (n κ : Nat) : Nat := n + κ + 1
def prepareActions (n κ : Nat) : List StraightLine.Action :=
  [.left .input, .left .input] ++ List.replicate (width n κ) (.right .output) ++ [.left .output]
def prepareCode (n κ : Nat) : Code := StraightLine.code (prepareActions n κ)
def copyCode (n κ : Nat) : Code := FixedWidthCopy.codeWith true true 0 (width n κ) 0
def suffixCells (κ : Nat) : List (Option Bool) := [none, some false] ++ List.replicate κ none
def suffixActions (n κ : Nat) : List StraightLine.Action :=
  [.right .output] ++ List.replicate n (.right .output) ++ FieldOverwrite.actions (suffixCells κ) ++
    List.replicate (n + κ + 2) (.left .output)
def suffixCode (n κ : Nat) : Code := StraightLine.code (suffixActions n κ)
def restoreCode (tail : Code) : Code :=
  CodeRelocation.host [.native (.moveRight .input)]
    (RightBlankSeek.code .input (RightBlankSeek.code .input tail))

theorem restoreCode_length (tail : Code) : (restoreCode tail).length = 9 + tail.length := by
  simp [restoreCode, RightBlankSeek.code, CodeRelocation.code_length, RightBlankSeek.body_length]
  omega
def code (n κ : Nat) (tail : Code) : Code :=
  CodeRelocation.host (prepareCode n κ)
    (LeftBlankAllocate.code (CodeRelocation.host (copyCode n κ)
      (restoreCode (CodeRelocation.host (suffixCode n κ) tail))))

def start (table : CompressionTable (Bits κ) (Bits n)) (fuel : Nat)
    (query : CompressionInput (Bits κ) (Bits n)) : Machine.Configuration :=
  { inputTape := UnaryFuel.tape fuel 0 ((SimulatorLookup.tableBits table).map some),
    outputTape := FixedWidthCopy.frontier (List.replicate (fuel + 2) none)
      ((compressionPacket query).map some ++ [some false, none]) }
def prepared (table : CompressionTable (Bits κ) (Bits n)) (fuel : Nat)
    (query : CompressionInput (Bits κ) (Bits n)) : Machine.Configuration :=
  { inputTape := FixedWidthCopy.backwardFrontier (none :: (SimulatorLookup.tableBits table).map some)
      (List.replicate fuel (some true) ++ [none]),
    outputTape := FixedWidthCopy.backwardFrontier [some false, none]
      ((compressionPacket query).reverse.map some ++ List.replicate (fuel + 2) none) }
def allocated (table : CompressionTable (Bits κ) (Bits n)) (fuel : Nat)
    (query : CompressionInput (Bits κ) (Bits n)) : Machine.Configuration :=
  { inputTape := { right := none :: List.replicate fuel (some true) ++ none :: (SimulatorLookup.tableBits table).map some },
    outputTape := (prepared table fuel query).outputTape }
def copied (table : CompressionTable (Bits κ) (Bits n)) (fuel : Nat)
    (query : CompressionInput (Bits κ) (Bits n)) : Machine.Configuration :=
  { inputTape := { right := (compressionPacket query).map some ++ none :: List.replicate fuel (some true) ++ none :: (SimulatorLookup.tableBits table).map some },
    outputTape := { left := List.replicate (fuel + 1) none, right := (compressionPacket query).map some ++ [some false, none] } }
def restored (table : CompressionTable (Bits κ) (Bits n)) (fuel : Nat)
    (query : CompressionInput (Bits κ) (Bits n)) : Machine.Configuration :=
  { inputTape := UnaryFuel.tapeWith (savedContext query) fuel 0 ((SimulatorLookup.tableBits table).map some),
    outputTape := (copied table fuel query).outputTape }
def finish (table : CompressionTable (Bits κ) (Bits n)) (fuel : Nat)
    (query : CompressionInput (Bits κ) (Bits n)) : Machine.Configuration :=
  { inputTape := (restored table fuel query).inputTape,
    outputTape := FixedWidthCopy.frontier (List.replicate (fuel + 2) none)
      (query.1.toList.map some ++ [none, some false] ++ List.replicate (κ + 1) none) }

theorem prepare_length (n κ : Nat) : (prepareActions n κ).length = width n κ + 3 := by simp [prepareActions]
theorem suffix_length (n κ : Nat) : (suffixActions n κ).length = 2 * n + 3 * κ + 7 := by
  simp [suffixActions, suffixCells, FieldOverwrite.length]; omega
theorem prepare_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code) (fuel : Nat)
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host (prepareCode n κ) tail) oracle) (width n κ + 3)
      (NativeCode.frame state trace (start table fuel query)) =
      PMF.pure (CodeRelocation.frame (prepareCode n κ).length (NativeCode.frame state trace (prepared table fuel query))) := by
  have hs := StraightLine.public_run oracle state trace [] (tail.map (CodeRelocation.instruction (prepareCode n κ).length))
    (prepareActions n κ) (start table fuel query) rfl rfl
  have hm := FixedWidthCopy.advance_output (compressionPacket query) (List.replicate (fuel + 2) none)
    [some false, none] ({ inputTape := (prepared table fuel query).inputTape, pc := 2 } : Machine.Configuration)
  simp only [compressionPacket_length] at hm
  have hn := SimulatorReconstruct.table_nonempty table
  have hne : (SimulatorLookup.tableBits table).map some ≠ [] := by simpa using hn
  have hinit : StraightLine.execute [.left .input, .left .input] (start table fuel query) =
      { pc := 2, inputTape := (prepared table fuel query).inputTape, outputTape := (start table fuel query).outputTape } := by
    cases hc : (SimulatorLookup.tableBits table).map some with
    | nil => contradiction
    | cons head rest =>
        cases fuel <;> simp [start, prepared, UnaryFuel.tape, UnaryFuel.tapeWith, UnaryFuel.counterWith,
          hc, StraightLine.execute, StraightLine.apply, Machine.Configuration.updateTape,
          Machine.Configuration.advance, FixedWidthCopy.frontier, ResponseLoading.fromCells,
          FixedWidthCopy.backwardFrontier, Tape.moveLeft, List.replicate_succ]
  have ha : StraightLine.execute (prepareActions n κ) (start table fuel query) =
      { prepared table fuel query with pc := width n κ + 3 } := by
    simp only [prepareActions, StraightLine.execute_append]
    rw [hinit]
    change StraightLine.execute [.left .output] (StraightLine.execute (List.replicate (n + κ + 1) (.right .output)) _) = _
    simp only [start]
    rw [hm]
    have hmove (cells : List (Option Bool)) : ({ left := cells, current := some false, right := [none] } : Tape).moveLeft =
        FixedWidthCopy.backwardFrontier [some false, none] cells := by cases cells <;> rfl
    simp [prepared, width, StraightLine.execute, StraightLine.apply, Machine.Configuration.advance,
      Machine.Configuration.updateTape, FixedWidthCopy.frontier, ResponseLoading.fromCells,
      hmove, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [ha] at hs
  simpa [prepareCode, CodeRelocation.host, NativeCode.frame, CodeRelocation.frame, CodeRelocation.control,
    Machine.Configuration.rebasePc, prepare_length, StraightLine.code, prepared] using hs

theorem allocate_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code) (fuel : Nat)
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) :
    TimedExecution.eval (Reification.timedStep (LeftBlankAllocate.code tail) oracle) (3 * fuel + 2)
      (NativeCode.frame state trace (prepared table fuel query)) =
      PMF.pure (CodeRelocation.frame 4 (NativeCode.frame state trace (allocated table fuel query))) := by
  simpa only [List.length_replicate, List.map_replicate, List.reverse_replicate, prepared, allocated] using
    LeftBlankAllocate.run oracle state trace tail (List.replicate fuel true)
      (none :: (SimulatorLookup.tableBits table).map some) (prepared table fuel query).outputTape

theorem copy_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code) (fuel : Nat)
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host (copyCode n κ) tail) oracle) (5 * width n κ)
      (NativeCode.frame state trace (allocated table fuel query)) =
      PMF.pure (CodeRelocation.frame (copyCode n κ).length (NativeCode.frame state trace (copied table fuel query))) := by
  have h := FixedWidthCopy.backward_run oracle state trace []
    (tail.map (CodeRelocation.instruction (copyCode n κ).length)) 0
    (none :: List.replicate fuel (some true) ++ none :: (SimulatorLookup.tableBits table).map some)
    [some false, none] (List.replicate (fuel + 2) none) (compressionPacket query).reverse
  simpa [copyCode, width, CodeRelocation.host, NativeCode.frame, CodeRelocation.frame,
    CodeRelocation.control, Machine.Configuration.rebasePc, allocated, prepared, copied,
    FixedWidthCopy.backwardFrontier, compressionPacket_length, List.replicate_succ,
    ← List.map_reverse, List.reverse_reverse] using h

theorem restore_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code) (fuel : Nat)
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) :
    TimedExecution.eval (Reification.timedStep (restoreCode tail) oracle) (3 * width n κ + 3 * fuel + 5)
      (NativeCode.frame state trace (copied table fuel query)) =
      PMF.pure (CodeRelocation.frame 9 (NativeCode.frame state trace (restored table fuel query))) := by
  let mid : Machine.Configuration := { inputTape := FixedWidthCopy.frontier [none] ((compressionPacket query).map some ++ none :: List.replicate fuel (some true) ++ none :: (SimulatorLookup.tableBits table).map some), outputTape := (copied table fuel query).outputTape }
  let inner : Machine.Configuration := { inputTape := FixedWidthCopy.frontier (none :: (compressionPacket query).reverse.map some ++ [none]) (List.replicate fuel (some true) ++ none :: (SimulatorLookup.tableBits table).map some), outputTape := (copied table fuel query).outputTape }
  have hp : TimedExecution.eval (Reification.timedStep (restoreCode tail) oracle) 1
      (NativeCode.frame state trace (copied table fuel query)) = PMF.pure (CodeRelocation.frame 1 (NativeCode.frame state trace mid)) := by
    have hnonempty : compressionPacket query ≠ [] := by have hlen := compressionPacket_length query; intro he; rw [he] at hlen; simp at hlen
    cases hc : compressionPacket query with
    | nil => contradiction
    | cons bit rest =>
        simp [restoreCode, copied, mid, hc, CodeRelocation.host, TimedExecution.eval, Reification.timedStep,
          Reification.terminal, NativeCode.frame, Reification.perform, Reification.action, transition,
          Machine.Instruction.next, Machine.Configuration.advance, Machine.Configuration.updateTape,
          Tape.moveRight, FixedWidthCopy.frontier, ResponseLoading.fromCells, CodeRelocation.frame,
          CodeRelocation.control, Machine.Configuration.rebasePc]
  have h₁ := RightBlankSeek.run oracle state trace .input (RightBlankSeek.code .input tail)
    (compressionPacket query) [none] (List.replicate fuel (some true) ++ none :: (SimulatorLookup.tableBits table).map some)
    (copied table fuel query).outputTape
  have h₂ := RightBlankSeek.run oracle state trace .input tail (List.replicate fuel true)
    (none :: (compressionPacket query).reverse.map some ++ [none]) ((SimulatorLookup.tableBits table).map some)
    (copied table fuel query).outputTape
  simp only [compressionPacket_length, LeftBlankRewind.put] at h₁
  simp only [List.length_replicate, List.map_replicate, List.reverse_replicate, LeftBlankRewind.put] at h₂
  have hs := SimulatorPredecessorExtract.seq_run oracle (RightBlankSeek.body .input) _ _ _ _ _ _ h₁ h₂
  have htime : 3 * (n + κ + 1) + 2 + (3 * fuel + 2) = 3 * width n κ + 3 * fuel + 4 := by unfold width; omega
  rw [htime] at hs
  have hs' : TimedExecution.eval (Reification.timedStep (RightBlankSeek.code .input (RightBlankSeek.code .input tail)) oracle)
      (3 * width n κ + 3 * fuel + 4) (NativeCode.frame state trace mid) =
      PMF.pure (CodeRelocation.frame 8 (NativeCode.frame state trace (restored table fuel query))) := by
    simpa [mid, width, restored, savedContext, UnaryFuel.tapeWith, UnaryFuel.counterWith,
      RightBlankSeek.code, RightBlankSeek.body_length, CodeRelocation.frame, CodeRelocation.control,
      NativeCode.frame, Machine.Configuration.rebasePc, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have h := SimulatorPredecessorExtract.seq_run oracle [.native (.moveRight .input)] _ _ _ _ _ _ hp hs'
  rw [show 1 + (3 * width n κ + 3 * fuel + 4) = 3 * width n κ + 3 * fuel + 5 from by omega] at h
  simpa [restoreCode, mid, inner, width, restored, savedContext, UnaryFuel.tapeWith, UnaryFuel.counterWith,
    RightBlankSeek.code, RightBlankSeek.body_length, CodeRelocation.frame, CodeRelocation.control,
    NativeCode.frame, Machine.Configuration.rebasePc, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem suffix_execute (fuel : Nat) (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) :
    StraightLine.execute (suffixActions n κ) (restored table fuel query) =
      { finish table fuel query with pc := 2 * n + 3 * κ + 7 } := by
  let before := List.replicate (fuel + 2) (none : Option Bool)
  let input := (restored table fuel query).inputTape
  let oldField := (query.2.1 :: query.2.2.toList).map some ++ [some false]
  have hfirst : StraightLine.execute [.right .output] (restored table fuel query) =
      { pc := 1, inputTape := input, outputTape := FixedWidthCopy.frontier before ((compressionPacket query).map some ++ [some false, none]) } := by
    have move (left cells : List (Option Bool)) : ({ left := left, right := cells } : Tape).moveRight =
        FixedWidthCopy.frontier (none :: left) cells := by cases cells <;> rfl
    simp [StraightLine.execute, StraightLine.apply, restored, copied, Machine.Configuration.updateTape,
      Machine.Configuration.advance, move, before, input, List.replicate_succ]
  have hnext := FixedWidthCopy.advance_output query.1.toList before (oldField ++ [none])
    ({ pc := 1, inputTape := input } : Machine.Configuration)
  simp only [Bits.length_toList] at hnext
  have hwrite := FieldOverwrite.execute (suffixCells κ) oldField
    (query.1.toList.reverse.map some ++ before) [none] ({ pc := 1 + n, inputTape := input } : Machine.Configuration)
    (by simp [suffixCells, oldField])
  have hlen : (suffixCells κ).length = κ + 2 := by simp [suffixCells]
  rw [hlen] at hwrite
  simp only [suffixActions, StraightLine.execute_append]
  rw [hfirst]
  have hpacket : (compressionPacket query).map some ++ [some false, none] =
      query.1.toList.map some ++ (oldField ++ [none]) := by simp [compressionPacket, oldField, List.map_append, List.append_assoc]
  rw [hpacket]
  rw [show StraightLine.execute (List.replicate n (.right .output)) _ = _ from hnext]
  rw [show StraightLine.execute (FieldOverwrite.actions (suffixCells κ)) _ = _ from hwrite]
  have hcells : (query.1.toList.map some ++ suffixCells κ).reverse ++ before =
      (suffixCells κ).reverse ++ (query.1.toList.reverse.map some ++ before) := by
    simp [List.reverse_append, ← List.map_reverse, List.append_assoc]
  have hrewind' : StraightLine.execute (List.replicate (n + κ + 2) (.left .output))
      { pc := (1 + n) + 2 * (κ + 2), inputTape := input,
        outputTape := FixedWidthCopy.frontier ((suffixCells κ).reverse ++ (query.1.toList.reverse.map some ++ before)) [none] } =
      { finish table fuel query with pc := 2 * n + 3 * κ + 7 } := by
    have hh := StraightLine.rewind_output (query.1.toList.map some ++ suffixCells κ) before [] none
      ({ pc := (1 + n) + 2 * (κ + 2), inputTape := input } : Machine.Configuration)
    simp only [List.length_append, List.length_map, Bits.length_toList] at hh
    rw [hlen, hcells] at hh
    rw [show (1 + n) + 2 * (κ + 2) + (n + (κ + 2)) = 2 * n + 3 * κ + 7 from by omega] at hh
    simpa [finish, input, before, StraightLine.rewindOutputTape, FixedWidthCopy.frontier,
      ResponseLoading.fromCells, suffixCells, List.append_assoc, ← List.replicate_succ',
      Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  exact hrewind'

theorem suffix_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code) (fuel : Nat)
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) :
    TimedExecution.eval (Reification.timedStep (CodeRelocation.host (suffixCode n κ) tail) oracle) (2 * n + 3 * κ + 7)
      (NativeCode.frame state trace (restored table fuel query)) =
      PMF.pure (CodeRelocation.frame (suffixCode n κ).length (NativeCode.frame state trace (finish table fuel query))) := by
  have h := StraightLine.public_run oracle state trace [] (tail.map (CodeRelocation.instruction (suffixCode n κ).length))
    (suffixActions n κ) (restored table fuel query) rfl rfl
  rw [suffix_execute, suffix_length] at h
  simpa [suffixCode, StraightLine.code, CodeRelocation.host, CodeRelocation.frame, CodeRelocation.control,
    NativeCode.frame, Machine.Configuration.rebasePc, finish, suffix_length] using h

theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (tail : Code) (fuel : Nat)
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) :
    TimedExecution.eval (Reification.timedStep (code n κ tail) oracle) (11 * n + 12 * κ + 6 * fuel + 26)
      (NativeCode.frame state trace (start table fuel query)) =
      PMF.pure (CodeRelocation.frame (code n κ []).length (NativeCode.frame state trace (finish table fuel query))) := by
  have hs := suffix_run oracle state trace tail fuel query table
  have hr := restore_run oracle state trace (CodeRelocation.host (suffixCode n κ) tail) fuel query table
  have hrestorePrefix : restoreCode (CodeRelocation.host (suffixCode n κ) tail) =
      CodeRelocation.host (restoreCode []) (CodeRelocation.host (suffixCode n κ) tail) := by
    simp only [restoreCode, RightBlankSeek.code, ← CodeRelocation.host_assoc]; simp [CodeRelocation.host]
  rw [hrestorePrefix] at hr
  have h₁ := SimulatorPredecessorExtract.seq_run oracle (restoreCode []) _ _ _ _ _ _ hr hs
  have h₂ := SimulatorPredecessorExtract.seq_run oracle (copyCode n κ) _ _ _ _ _ _
    (copy_run oracle state trace (restoreCode (CodeRelocation.host (suffixCode n κ) tail)) fuel query table)
    (by simpa only [← hrestorePrefix] using h₁)
  have h₃ := SimulatorPredecessorExtract.seq_run oracle LeftBlankAllocate.body _ _ _ _ _ _
    (allocate_run oracle state trace (CodeRelocation.host (copyCode n κ) (restoreCode (CodeRelocation.host (suffixCode n κ) tail))) fuel query table) h₂
  have h := SimulatorPredecessorExtract.seq_run oracle (prepareCode n κ) _ _ _ _ _ _
    (prepare_run oracle state trace (LeftBlankAllocate.code (CodeRelocation.host (copyCode n κ) (restoreCode (CodeRelocation.host (suffixCode n κ) tail)))) fuel query table) h₃
  have ht : (width n κ + 3) + (3 * fuel + 2 + (5 * width n κ + (3 * width n κ + 3 * fuel + 5 + (2 * n + 3 * κ + 7)))) =
      11 * n + 12 * κ + 6 * fuel + 26 := by unfold width; omega
  rw [ht] at h
  simpa only [code, LeftBlankAllocate.code, hrestorePrefix, CodeRelocation.frame, CodeRelocation.control,
    NativeCode.frame, Machine.Configuration.rebasePc, CodeRelocation.code_length, restoreCode_length,
    List.length_nil, Nat.add_zero, Nat.add_assoc] using h

theorem code_length (n κ : Nat) (tail : Code) : (code n κ tail).length = 10 * n + 11 * κ + 31 + tail.length := by
  simp [code, LeftBlankAllocate.code, LeftBlankAllocate.body, copyCode, FixedWidthCopy.codeWith_length,
    prepareCode, prepare_length, suffixCode, suffix_length, restoreCode_length,
    CodeRelocation.code_length, StraightLine.code, width]
  omega

theorem link (n κ : Nat) (tail : Code) : code n κ tail = CodeRelocation.host (code n κ []) tail := by
  simp only [code, LeftBlankAllocate.code, restoreCode, RightBlankSeek.code, ← CodeRelocation.host_assoc]
  simp [CodeRelocation.host]

theorem code_native (n κ : Nat) (tail : Code) (ht : ∀ op ∈ tail, ∃ native, op = .native native) :
    ∀ op ∈ code n κ tail, ∃ native, op = .native native := by
  have straight (actions : List StraightLine.Action) : ∀ op ∈ StraightLine.code actions, ∃ native, op = .native native := by
    intro op hm; obtain ⟨action, _, rfl⟩ := List.mem_map.mp hm; exact ⟨_, rfl⟩
  apply CodeRelocation.host_native
  · exact straight _
  apply CodeRelocation.host_native
  · exact LeftBlankAllocate.body_native
  apply CodeRelocation.host_native
  · exact FixedWidthCopy.codeWith_native _ _ _ _ _
  apply CodeRelocation.host_native
  · intro op hm; exact ⟨_, by simpa using hm⟩
  apply CodeRelocation.host_native
  · exact RightBlankSeek.body_native _
  apply CodeRelocation.host_native
  · exact RightBlankSeek.body_native _
  exact CodeRelocation.host_native _ _ (straight _) ht

theorem blank_tail (cells : List (Option Bool)) (blanks i : Nat) :
    (cells ++ List.replicate blanks none).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => exact (Tape.blank_padding_equivalent [] blanks).2.2 i
  | cons cell rest ih =>
      cases i with
      | zero => rfl
      | succ i => simpa only [List.cons_append, List.getD_cons_succ] using ih i

theorem frontier_padding (before cells : List (Option Bool)) (blanks : Nat) (hn : cells ≠ []) :
    (FixedWidthCopy.frontier before (cells ++ List.replicate blanks none)).Equivalent (FixedWidthCopy.frontier before cells) := by
  cases cells with
  | nil => contradiction
  | cons cell rest => exact ⟨rfl, fun _ => rfl, blank_tail rest blanks⟩

theorem finish_equivalent (table : CompressionTable (Bits κ) (Bits n)) (fuel : Nat)
    (query : CompressionInput (Bits κ) (Bits n)) :
    (finish table fuel query).Equivalent
      (SimulatorReconstruct.startWith (savedContext query) table fuel 0 query.1 []) := by
  refine ⟨rfl, rfl, Tape.Equivalent.refl _, ?_⟩
  exact (SimulatorFuelPrepare.blank_frontier_equivalent (fuel + 2)
    ((query.1.toList.map some ++ [none, some false]) ++ List.replicate (κ + 1) none)).trans
    (frontier_padding [none] (query.1.toList.map some ++ [none, some false]) (κ + 1) (by simp))

theorem saved_key (query : CompressionInput (Bits κ) (Bits n)) (input : Tape)
    (h : ∃ remaining, SimulatorReconstruct.tapeContent input = (savedContext query).reverse ++ remaining) :
    input.bits.take (width n κ) = compressionPacket query := by
  obtain ⟨remaining, h⟩ := h
  have hb : input.bits = (SimulatorReconstruct.tapeContent input).filterMap id := by
    simp [Tape.bits, SimulatorReconstruct.tapeContent, List.filterMap_append]
  rw [hb, h]
  have hc : ((savedContext query).reverse).filterMap id = compressionPacket query := by
    simp [savedContext, List.filterMap_map]
  rw [List.filterMap_append, hc]
  have hl : (compressionPacket query).length = width n κ := compressionPacket_length query
  rw [← hl, List.take_left]

def view (width κ : Nat) (frame : Configuration State) :
    Option (State × List (List Bool × List Bool) × Bool × List Bool × Option (List (Bits κ))) :=
  match frame.control with
  | .running machine => some (frame.state, frame.reverseTrace, machine.halted,
      machine.inputTape.bits.take width, SimulatorReconstruct.readResult κ machine)
  | _ => none

theorem view_equivalent {State : Type*} (width κ : Nat) (first second : Configuration State)
    (h : NativeCode.CellEquivalent first second) : view width κ first = view width κ second := by
  cases h with
  | finished => rfl
  | running state trace first second he =>
      have hr := SimulatorFuelPrepare.observe_equivalent κ _ _ (.running state trace first second he)
      simp only [SimulatorReconstruct.observe, NativeCode.frame] at hr
      simp only [view, NativeCode.frame, he.2.1, he.2.2.1.bits, hr]

theorem view_frame {State : Type*} (width κ base : Nat) :
    view (State := State) width κ ∘ CodeRelocation.frame base = view width κ := by
  funext frame
  cases hc : frame.control <;>
    simp [view, CodeRelocation.frame, CodeRelocation.control, hc, SimulatorReconstruct.readResult,
      Machine.Configuration.rebasePc]

/-- Jointly observe stopping, full external state/history, the saved original
packet, and the reconstructed message under the same actual emitted code. -/
theorem with_reconstruct_law (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (initial : Bits n) (fuel : Nat)
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n)) :
    (TimedExecution.eval (Reification.timedStep (code n κ (SimulatorReconstruct.code initial κ)) oracle)
      ((11 * n + 12 * κ + 6 * fuel + 26) + SimulatorReconstruct.budget table fuel 0)
      (NativeCode.frame state trace (start table fuel query))).map (view (width n κ) κ) =
      PMF.pure (some (state, trace, true, compressionPacket query, messagePrefix initial table fuel query.1)) := by
  have hp := run oracle state trace (SimulatorReconstruct.code initial κ) fuel query table
  obtain ⟨result, hr, hout⟩ := SimulatorReconstruct.run_at_budget (savedContext := savedContext query)
    oracle state trace initial table fuel 0 query.1 []
  have hkey := saved_key query result.inputTape hout.2.2.2.2
  have hread := SimulatorReconstruct.read_represents table _ result hout
  rw [MessagePrefixLoop.run_eq] at hread
  simp at hread
  have he := finish_equivalent table fuel query
  have eq := NativeCode.eval_map_eq_of_cellEquivalent (SimulatorReconstruct.code initial κ)
    (SimulatorReconstruct.code_native _ _) oracle (SimulatorReconstruct.budget table fuel 0)
    (NativeCode.frame state trace (finish table fuel query))
    (NativeCode.frame state trace (SimulatorReconstruct.startWith (savedContext query) table fuel 0 query.1 []))
    (.running state trace _ _ he) (view (width n κ) κ) (view_equivalent _ _)
  rw [TimedExecution.eval_add, hp, PMF.pure_bind, link, CodeRelocation.eval, PMF.map_comp,
    view_frame, eq, hr, PMF.pure_map]
  simp only [view, NativeCode.frame, hout.1, hkey, hread]

end Foundation.Hash.Native.SimulatorKeyProtect
