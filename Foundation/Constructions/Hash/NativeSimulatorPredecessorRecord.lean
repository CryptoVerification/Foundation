import Foundation.Constructions.Hash.NativeSimulatorKeyComparison
import Foundation.Crypto.Semantics.Oracle.RawTapeEquality
import Foundation.Crypto.Semantics.Oracle.CodeRelocation

/-! The response-field comparison needed by ordered predecessor search.
The original table encoding is retained: skip the marker and delimited key,
then compare the raw response with the runtime target. No delimiter is inserted
into the private table. Marker filtering and the table loop are separate stages. -/
namespace Foundation.Hash.Native.SimulatorPredecessorRecord
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n κ : Nat}

def header (entry : CompressionInput (Bits κ) (Bits n) × Bits n) : List Bool :=
  true :: FiniteBitEncoding.delimit (compressionPacket entry.1)

theorem header_length (entry : CompressionInput (Bits κ) (Bits n) × Bits n) :
    (header entry).length = 2 * (n + κ + 1) + 2 := by
  simp [header, FiniteBitEncoding.delimit_length, compressionPacket_length]

def skipActions (n κ : Nat) : List StraightLine.Action :=
  List.replicate (2 * (n + κ + 1) + 2) (.right .input)

def code (n κ : Nat) : Code :=
  CodeRelocation.host (StraightLine.code (skipActions n κ)) RawTapeEquality.code

theorem code_length (n κ : Nat) : (code n κ).length = 2 * (n + κ + 1) + 16 := by
  simp only [code, CodeRelocation.code_length, StraightLine.code, skipActions,
    RawTapeEquality.code, NativeCode.code, List.length_map, List.length_replicate,
    RawTapeEquality.program_length]

theorem code_native (n κ : Nat) : ∀ i ∈ code n κ, ∃ op, i = .native op := by
  apply CodeRelocation.host_native _ _ _ RawTapeEquality.code_native
  intro i hi
  simp only [StraightLine.code, List.mem_map] at hi
  obtain ⟨action, _, he⟩ := hi
  exact ⟨StraightLine.instruction action, he.symm⟩

theorem steps_bound (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n) :
    2 * (n + κ + 1) + 2 + RawTapeEquality.steps entry.2.toList target.toList ≤
      7 * n + 2 * κ + 9 := by
  have h := RawTapeEquality.steps_bound entry.2.toList target.toList (by simp)
  simp only [Bits.length_toList] at h
  omega

def comparisonInput (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) : RawTapeEquality.Input where
  candidate := entry.2.toList
  query := target.toList
  width := by simp
  leftInput := (header entry).reverse.map some ++ beforeInput
  leftOutput := beforeOutput
  inputTail := inputTail
  outputTail := outputTail

/-- Compare a table response against a runtime chaining target. The full encoded
key and response survive on the input tape, and the next marker remains the head. -/
theorem run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool))
    (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (code n κ) oracle)
      (2 * (n + κ + 1) + 2 + RawTapeEquality.steps entry.2.toList target.toList)
      (⟨state, .running { inputTape := FixedWidthCopy.frontier beforeInput ((SimulatorLookup.entryBits entry).map some ++ inputTail), outputTape := FixedWidthCopy.frontier beforeOutput (target.toList.map some ++ none :: outputTail) }, trace⟩ : Configuration State) =
      PMF.pure (CodeRelocation.frame (StraightLine.code (skipActions n κ)).length
        (NativeCode.frame state trace (RawTapeEquality.result (comparisonInput entry target beforeInput beforeOutput inputTail outputTail)))) := by
  let input := comparisonInput entry target beforeInput beforeOutput inputTail outputTail
  have hentry : SimulatorLookup.entryBits entry = header entry ++ entry.2.toList := rfl
  have hprefix := StraightLine.public_run oracle state trace []
    (RawTapeEquality.code.map (CodeRelocation.instruction (StraightLine.code (skipActions n κ)).length))
    (skipActions n κ)
    { inputTape := FixedWidthCopy.frontier beforeInput ((SimulatorLookup.entryBits entry).map some ++ inputTail), outputTape := FixedWidthCopy.frontier beforeOutput (target.toList.map some ++ none :: outputTail) }
    rfl rfl
  simp only [List.nil_append, skipActions, List.length_replicate] at hprefix
  have hs := FixedWidthCopy.advance_input (header entry) beforeInput (entry.2.toList.map some ++ inputTail)
    ({ outputTape := FixedWidthCopy.frontier beforeOutput (target.toList.map some ++ none :: outputTail) } : Machine.Configuration)
  rw [header_length] at hs
  rw [hentry, List.map_append, List.append_assoc] at hprefix
  rw [hs] at hprefix
  have hcode : StraightLine.code (List.replicate (2 * (n + κ + 1) + 2) (.right .input)) ++
      RawTapeEquality.code.map (CodeRelocation.instruction (StraightLine.code (skipActions n κ)).length) = code n κ := rfl
  simp only [skipActions] at hcode
  rw [hcode] at hprefix
  rw [hentry, List.map_append, List.append_assoc]
  rw [TimedExecution.eval_add, hprefix, PMF.pure_bind]
  have hplaced := CodeRelocation.eval (StraightLine.code (skipActions n κ)) RawTapeEquality.code oracle
    (RawTapeEquality.steps entry.2.toList target.toList)
    (NativeCode.frame state trace (RawTapeEquality.start input))
  have hstart : (⟨state, .running { pc := 0 + (2 * (n + κ + 1) + 2), inputTape := FixedWidthCopy.frontier ((header entry).reverse.map some ++ beforeInput) (entry.2.toList.map some ++ inputTail), outputTape := FixedWidthCopy.frontier beforeOutput (target.toList.map some ++ none :: outputTail) }, trace⟩ : Configuration State) =
      CodeRelocation.frame (StraightLine.code (skipActions n κ)).length
        (NativeCode.frame state trace (RawTapeEquality.start input)) := by
    simp [input, comparisonInput, RawTapeEquality.start, NativeCode.frame, CodeRelocation.frame,
      CodeRelocation.control, Machine.Configuration.rebasePc, StraightLine.code, skipActions]
  rw [hstart]
  change TimedExecution.eval (Reification.timedStep
    (CodeRelocation.host (StraightLine.code (skipActions n κ)) RawTapeEquality.code) oracle) _ _ = _
  rw [hplaced]
  dsimp only [input, RawTapeEquality.start, NativeCode.frame, comparisonInput]
  rw [RawTapeEquality.run oracle state trace entry.2.toList target.toList (by simp), PMF.pure_map]
  rfl

theorem status (entry : CompressionInput (Bits κ) (Bits n) × Bits n) (target : Bits n)
    (beforeInput beforeOutput inputTail outputTail : List (Option Bool)) :
    (RawTapeEquality.result (comparisonInput entry target beforeInput beforeOutput inputTail outputTail)).outputTape.current =
      some (decide (entry.2 = target)) := by
  rw [RawTapeEquality.result_status]
  simp only [comparisonInput, Bits.toList, List.ofFn_inj]

end Foundation.Hash.Native.SimulatorPredecessorRecord
