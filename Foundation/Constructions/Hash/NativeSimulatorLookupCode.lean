import Foundation.Constructions.Hash.NativeSimulatorKeyComparison
import Foundation.Crypto.Semantics.Oracle.NativeSubroutine
import Foundation.Crypto.Semantics.Oracle.FixedWidthCopy

/-! Sequential compression-table lookup code. The body depends only on the
key and digest widths. Table records and query bits are read at run time.
This file certifies the code layout and comparison return; the loop's
List.lookup correspondence is a separate obligation. -/
namespace Foundation.Hash.Native.SimulatorLookup
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

/-- Restore the comparison delimiter, skip the digest and rewind the query. -/
def skipActions (n κ : Nat) : List StraightLine.Action :=
  [.write .input (some false), .right .input] ++
    List.replicate n (.right .input) ++ List.replicate (n + κ + 1) (.left .output)

def foundActions : List StraightLine.Action :=
  [.write .input (some false), .right .input,
   .write .output (some true), .right .output]

/-- The query is retained; its following false cell is the absent flag. -/
def missingActions (n κ : Nat) : List StraightLine.Action :=
  List.replicate (n + κ + 1) (.right .output) ++
    [.write .output (some false), .right .output]

def foundPc (n κ : Nat) : Nat := 64 + 2 * n + κ + 1
def copyPc (n κ : Nat) : Nat := foundPc n κ + 4
def missingPc (n κ : Nat) : Nat := copyPc n κ + 7 * n + 1
def headerPc (n κ : Nat) : Nat := missingPc n κ + (n + κ + 1) + 3
def faultPc (n κ : Nat) : Nat := headerPc n κ + 3

def lookupBody (n κ : Nat) : Code :=
  [.native (.branch .input (faultPc n κ) 61 (foundPc n κ))] ++
  StraightLine.code (skipActions n κ) ++ [.native (.jump (headerPc n κ))] ++
  StraightLine.code foundActions ++ FixedWidthCopy.code (copyPc n κ) n (faultPc n κ) ++
  [.native .halt] ++ StraightLine.code (missingActions n κ) ++ [.native .halt]

def lookupTail (n κ : Nat) : Code :=
  lookupBody n κ ++ [.native (.branch .input (faultPc n κ) (missingPc n κ) (headerPc n κ + 1)),
   .native (.moveRight .input), .native (.jump 0), .native .halt]

/-- Entry is at headerPc, not at the equality subroutine at zero. -/
def lookupCode (n κ : Nat) : Code :=
  NativeCode.subroutinePrefix DelimitedTapeEquality.program ++ lookupTail n κ

@[simp] theorem skipActions_length (n κ : Nat) :
    (skipActions n κ).length = 2 * n + κ + 3 := by simp [skipActions]; omega
@[simp] theorem foundActions_length : foundActions.length = 4 := rfl
@[simp] theorem missingActions_length (n κ : Nat) :
    (missingActions n κ).length = n + κ + 3 := by simp [missingActions]

theorem lookupCode_length (n κ : Nat) : (lookupCode n κ).length = 78 + 10 * n + 2 * κ := by
  simp [lookupCode, lookupTail, lookupBody, NativeCode.subroutinePrefix_length, StraightLine.code]
  omega

/-- Widths alone determine the finite code; no ideal compression calls or
local random sampling occur during lookup. -/
theorem lookupCode_native (n κ : Nat) :
    ∀ instruction ∈ lookupCode n κ, ∃ native, instruction = .native native := by
  have copier : ∀ base width fault, ∀ instruction ∈ FixedWidthCopy.code base width fault,
      ∃ native, instruction = .native native := by
    intro base width fault
    induction width generalizing base with
    | zero => simp [FixedWidthCopy.code]
    | succ width ih =>
        intro instruction member
        simp only [FixedWidthCopy.code, List.mem_append] at member
        rcases member with first | rest
        · simp only [FixedWidthCopy.cellCode, FixedWidthCopy.cellCodeWith, List.mem_cons, List.not_mem_nil, or_false] at first
          rcases first with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
        · exact ih _ instruction rest
  intro instruction member
  simp only [lookupCode, lookupTail, lookupBody, List.mem_append, NativeCode.subroutinePrefix,
    NativeCode.code, StraightLine.code, List.mem_map] at member
  have copyNative := copier (copyPc n κ) n (faultPc n κ) instruction
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  aesop

theorem lookupBody_length (n κ : Nat) : (lookupBody n κ).length + 60 = headerPc n κ := by
  simp only [lookupBody, List.length_append, List.length_singleton, StraightLine.code,
    List.length_map, skipActions_length, foundActions_length, FixedWidthCopy.code_length,
    missingActions_length]
  simp only [headerPc, missingPc, copyPc, foundPc]
  omega

theorem lookup_header_instruction (n κ : Nat) :
    (lookupCode n κ)[headerPc n κ]? = some (.native
      (.branch .input (faultPc n κ) (missingPc n κ) (headerPc n κ + 1))) := by
  have prefixLength : (NativeCode.subroutinePrefix DelimitedTapeEquality.program ++ lookupBody n κ).length =
      headerPc n κ := by
    rw [List.length_append, NativeCode.subroutinePrefix_length, DelimitedTapeEquality.code_length]
    have h := lookupBody_length n κ
    omega
  unfold lookupCode lookupTail
  rw [← List.append_assoc]
  change ((NativeCode.subroutinePrefix DelimitedTapeEquality.program ++ lookupBody n κ) ++ _)[headerPc n κ]? = _
  rw [← prefixLength, List.getElem?_append_right (by omega), Nat.sub_self]
  rfl

/-- The table marker is inspected by an actual native branch. False means
end of table; true means that the next cells contain an entry key. -/
theorem lookup_header_step {State : Type*} (n κ : Nat)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (machine : Machine.Configuration) (bit : Bool)
    (pc : machine.pc = headerPc n κ) (active : machine.halted = false)
    (current : machine.inputTape.current = some bit) :
    Reification.timedStep (lookupCode n κ) oracle (NativeCode.frame state trace machine) =
      PMF.pure (NativeCode.frame state trace
        { machine with pc := if bit then headerPc n κ + 1 else missingPc n κ }) := by
  have instruction : (lookupCode n κ)[machine.pc]? = some (.native
      (.branch .input (faultPc n κ) (missingPc n κ) (headerPc n κ + 1))) := by
    rw [pc]; exact lookup_header_instruction n κ
  cases bit <;> simp [Reification.timedStep, Reification.terminal, NativeCode.frame,
    Reification.perform, Reification.action, transition, active, instruction,
    Machine.Instruction.next, Machine.Configuration.tape, current]

/-- The equality routine returns into the actual decision branch, retaining
both physical tapes and the opaque surrounding state/history. -/
theorem lookup_comparison_first_return {State : Type*} (n κ : Nat)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (input : DelimitedTapeEquality.Input) :
    runToBoundary (Reification.timedStep (lookupCode n κ) oracle)
      (NativeCode.returnBoundary 60) (7 * input.candidate.length + 3)
      (NativeCode.frame state trace (DelimitedTapeEquality.start input)) =
      PMF.pure (NativeCode.frame state trace ((DelimitedTapeEquality.finish input).resumeAt 60),
        7 * input.candidate.length + 3) := by
  have h := NativeCode.subroutine_first_joint DelimitedTapeEquality.component
    (lookupTail n κ) oracle state trace input
  rw [DelimitedTapeEquality.component_first_joint, PMF.pure_map] at h
  change runToBoundary (Reification.timedStep (lookupCode n κ) oracle)
      (NativeCode.returnBoundary 60) (7 * input.candidate.length + 3)
      (NativeCode.frame state trace (DelimitedTapeEquality.start input)) = _ at h
  simpa only [Machine.Program.subroutineState,
    show (DelimitedTapeEquality.finish input).halted = true from rfl, ↓reduceIte,
    show DelimitedTapeEquality.component.procedure.code.length + 1 = 60 from rfl] using h

/-- At the exact return time, the whole native execution has the same
physical frame, not just the equality decision. -/
theorem lookup_comparison_run {State : Type*} (n κ : Nat)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (input : DelimitedTapeEquality.Input) :
    TimedExecution.eval (Reification.timedStep (lookupCode n κ) oracle)
      (7 * input.candidate.length + 3)
      (NativeCode.frame state trace (DelimitedTapeEquality.start input)) =
      PMF.pure (NativeCode.frame state trace ((DelimitedTapeEquality.finish input).resumeAt 60)) := by
  rw [runToBoundary_law _ (NativeCode.returnBoundary 60)
    (7 * input.candidate.length + 3) (7 * input.candidate.length + 3) _ (by omega),
    lookup_comparison_first_return, PMF.pure_bind, Nat.sub_self, TimedExecution.eval]

/-- Rewinding a retained query restores its exact tape, including its
old left prefix and the response-flag placeholder. No free reset occurs. -/
theorem comparison_query_rewind (input : DelimitedTapeEquality.Input)
    (placeholder : input.suffix = [false]) :
    StraightLine.execute (List.replicate input.query.length (.left .output))
      ((DelimitedTapeEquality.finish input).resumeAt 60) =
      { (DelimitedTapeEquality.finish input).resumeAt 60 with
        pc := 60 + input.query.length
        outputTape := { Tape.ofBits (input.query ++ [false]) with left := input.beforeOutput } } := by
  have h := StraightLine.rewind_output (input.query.map some) input.beforeOutput [] (some false)
    ((DelimitedTapeEquality.finish input).resumeAt 60)
  have layout : ((DelimitedTapeEquality.finish input).resumeAt 60).outputTape =
      { left := (input.query.map some).reverse ++ input.beforeOutput,
        current := some false, right := [] } := by
    simp only [Configuration.resumeAt, DelimitedTapeEquality.output_layout, placeholder,
      Tape.ofBits, List.map_nil, List.map_reverse]
  have same : ({ (DelimitedTapeEquality.finish input).resumeAt 60 with
      outputTape := { left := (input.query.map some).reverse ++ input.beforeOutput, current := some false, right := [] } } : Machine.Configuration) =
      (DelimitedTapeEquality.finish input).resumeAt 60 := by rw [← layout]
  rw [same] at h
  cases queryEq : input.query <;>
    simpa [StraightLine.rewindOutputTape, Tape.ofBits, Configuration.resumeAt,
      List.map_append, queryEq] using h

end Foundation.Hash.Native.SimulatorLookup
