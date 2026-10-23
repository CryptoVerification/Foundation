import Foundation.Constructions.Symmetric.RandomFunctionMACNativeCorrectness

/-! Eliminate the second-tag store only when the third-tag store will
overwrite it. Every oracle call, including the repeated request, remains.
The finite code changes; arbitrary oracle replies need no cache assumption. -/
namespace Foundation.Symmetric.RandomFunctionMACNativeOptimized
open Foundation.Probability CryptoOracle CryptoOracle.Interactive TimedExecution Machine
open RandomFunctionMACNativeCaller
open RandomFunctionMACNativeCaller.Native (dynamicPacket saveTag lastPacket compareBits
  memory machineAt returned residue extendTrace afterCoin firstCall comparisonPairs)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def code : Code :=
  [.native (.randomBit .input)] ++
  dynamicPacket 1 250 .input true false false ++
  dynamicPacket 16 250 .output false true true ++
  [.native (.branch .input 250 32 106)] ++ saveTag 32 250 ++
  dynamicPacket 106 250 .input true false false ++
  [.native (.branch .input 250 196 122)] ++ saveTag 122 250 ++ lastPacket ++
  [.native (.moveRight .input)] ++ compareBits 8 208 250 ++
  [.native (.write .output true), .native .halt,
   .native (.write .output false), .native .halt]

theorem code_length : code.length = 252 := by decide_cbv
theorem code_changed : code ≠ RandomFunctionMACNativeCaller.Native.code := by
  intro same
  have lengths := congrArg List.length same
  rw [code_length, RandomFunctionMACNativeCaller.Native.code_length] at lengths
  contradiction

theorem call_addresses :
    ((code.zipIdx).filter (fun entry => entry.1 == .call)).map Prod.snd = [15, 30, 120, 206] := by decide_cbv

def savedSecond (coin : Bool) (second : Tag) : Option Tag := if coin then none else some second
def secondCall (coin : Bool) (first : Tag) := RandomFunctionMACNativeCaller.Native.secondCall coin first
def thirdCall (coin : Bool) (saved : Option Tag) (second : Tag) : Machine.Configuration :=
  machineAt 120 coin saved (RequestExport.packetTape [] (residue second) (encodeMessage (firstMessage coin)))
def lastCall (coin : Bool) (candidate repeated : Tag) : Machine.Configuration :=
  machineAt 206 coin (some candidate) (RequestExport.packetTape [] (residue repeated) (encodeMessage 7))

macro "optimized_native_step" : tactic => `(tactic|
  (rw [NativeDeterministic.run]
   all_goals simp_all [NativeDeterministic.next?, code, dynamicPacket, saveTag,
     RandomFunctionMACNativeCaller.Native.copyBits, RandomFunctionMACNativeCaller.Native.copyBit, lastPacket,
     Machine.Instruction.next, Machine.Configuration.tape, Machine.Configuration.updateTape,
     Machine.Configuration.advance, Tape.write, Tape.moveLeft, Tape.moveRight]))

theorem first_setup_checked (coin : Bool) :
    NativeDeterministic.run code 12 (afterCoin coin) = some (firstCall coin) := by
  cases coin <;> decide_cbv

theorem second_setup_checked (coin : Bool) (first : Tag) :
    NativeDeterministic.run code 12 (returned 16 coin none first) = some (secondCall coin first) := by
  by_cases even : first.val % 2 = 0
  · simp only [returned, machineAt, memory, secondCall, RandomFunctionMACNativeCaller.Native.secondCall,
      residue, ResponseLoading.loaded, ResponseLoading.fromCells, RequestExport.packetTape,
      encodeMessage, encodeTag, secondMessage, Machine.Binary.encode]
    repeat' optimized_native_step
  · have odd : first.val % 2 = 1 := by omega
    simp only [returned, machineAt, memory, secondCall, RandomFunctionMACNativeCaller.Native.secondCall,
      residue, ResponseLoading.loaded, ResponseLoading.fromCells, RequestExport.packetTape,
      encodeMessage, encodeTag, secondMessage, Machine.Binary.encode]
    repeat' optimized_native_step

theorem third_setup_checked (coin : Bool) (saved : Option Tag) (second : Tag) :
    NativeDeterministic.run code 12 (returned 106 coin saved second) = some (thirdCall coin saved second) := by
  cases coin <;> cases saved <;>
    simp only [returned, machineAt, memory, thirdCall, residue, ResponseLoading.loaded,
      ResponseLoading.fromCells, RequestExport.packetTape, encodeMessage, encodeTag, firstMessage, Machine.Binary.encode] <;>
    repeat' optimized_native_step

theorem last_setup_checked (coin : Bool) (candidate repeated : Tag) :
    NativeDeterministic.run code 10 (returned 196 coin (some candidate) repeated) = some (lastCall coin candidate repeated) := by
  simp only [returned, machineAt, memory, lastCall, residue, ResponseLoading.loaded,
    ResponseLoading.fromCells, RequestExport.packetTape, encodeMessage, encodeTag, Machine.Binary.encode]
  repeat' optimized_native_step

def saveAddress (third : Bool) : Nat := if third then 122 else 32
def copyAddress (third : Bool) : Nat := if third then 123 else 33
def savedAddress (third : Bool) : Nat := if third then 196 else 106

theorem copy_locations (third : Bool) (index : Fin 8) :
    NativeCopyBlock.Located code (copyAddress third + 7 * index.val) 250 := by
  fin_cases index <;> cases third <;> constructor <;> decide_cbv

theorem save_enter_checked (third coin : Bool) (saved : Option Tag) (tag : Tag) :
    NativeDeterministic.run code 1 (returned (saveAddress third) coin saved tag) =
      some (NativeCopyBlock.manyStart (copyAddress third) (memory coin saved).moveRight [] [] (encodeTag tag)) := by
  cases third <;>
    simp only [returned, machineAt, saveAddress, copyAddress, NativeCopyBlock.manyStart,
      ResponseLoading.loaded, ResponseLoading.fromCells, RequestExport.packetTape] <;>
    repeat' optimized_native_step

theorem save_rewind_checked (third coin : Bool) (saved : Option Tag) (tag : Tag) :
    NativeDeterministic.run code 17
      (NativeCopyBlock.manyFinish (copyAddress third) (memory coin saved).moveRight [] [] (encodeTag tag)) =
      some (returned (savedAddress third) coin (some tag) tag) := by
  cases third <;> cases saved <;>
    simp only [returned, machineAt, memory, copyAddress, savedAddress, NativeCopyBlock.manyFinish,
      NativeCopyBlock.written, encodeTag, Machine.Binary.encode, List.length_cons, List.length_nil,
      ResponseLoading.loaded, ResponseLoading.fromCells, RequestExport.packetTape] <;>
    repeat' optimized_native_step

theorem save_tag_checked (third coin : Bool) (saved : Option Tag) (tag : Tag) :
    NativeDeterministic.run code 58 (returned (saveAddress third) coin saved tag) =
      some (returned (savedAddress third) coin (some tag) tag) := by
  have locations : ∀ index, index < (encodeTag tag).length →
      NativeCopyBlock.Located code (copyAddress third + 7 * index) 250 := by
    intro index inside
    exact copy_locations third ⟨index, by simpa only [tag_width] using inside⟩
  have copy := NativeCopyBlock.many_checked code (copyAddress third) 250
    (memory coin saved).moveRight [] [] (encodeTag tag) locations
  have copy40 : NativeDeterministic.run code 40
      (NativeCopyBlock.manyStart (copyAddress third) (memory coin saved).moveRight [] [] (encodeTag tag)) =
      some (NativeCopyBlock.manyFinish (copyAddress third) (memory coin saved).moveRight [] [] (encodeTag tag)) := by
    simpa only [tag_width, Nat.reduceMul] using copy
  rw [show 58 = 1 + (40 + 17) by rfl, NativeDeterministic.run_add, save_enter_checked,
    Option.bind_some, NativeDeterministic.run_add, copy40, Option.bind_some, save_rewind_checked]

theorem select_second_checked (coin : Bool) (second : Tag) :
    NativeDeterministic.run code (if coin then 1 else 59) (returned 31 coin none second) =
      some (returned 106 coin (savedSecond coin second) second) := by
  cases coin with
  | true =>
      simp only [if_true, savedSecond, returned, machineAt, memory]
      repeat' optimized_native_step
  | false =>
      change NativeDeterministic.run code (1 + 58) (returned 31 false none second) = _
      rw [NativeDeterministic.run_add]
      have head : NativeDeterministic.run code 1 (returned 31 false none second) =
          some (returned 32 false none second) := by
        simp only [returned, machineAt, memory]
        repeat' optimized_native_step
      rw [head, Option.bind_some]
      exact save_tag_checked false false none second

theorem select_candidate_checked (coin : Bool) (second repeated : Tag) :
    NativeDeterministic.run code (if coin then 59 else 1) (returned 121 coin (savedSecond coin second) repeated) =
      some (returned 196 coin (some (if coin then repeated else second)) repeated) := by
  cases coin with
  | false =>
      simp only [Bool.false_eq_true, if_false, savedSecond, returned, machineAt, memory]
      repeat' optimized_native_step
  | true =>
      change NativeDeterministic.run code (1 + 58) (returned 121 true none repeated) = _
      rw [NativeDeterministic.run_add]
      have head : NativeDeterministic.run code 1 (returned 121 true none repeated) =
          some (returned 122 true none repeated) := by
        simp only [returned, machineAt, memory]
        repeat' optimized_native_step
      rw [head, Option.bind_some]
      exact save_tag_checked true true none repeated

def comparisonStart (coin : Bool) (candidate actual : Tag) : Machine.Configuration :=
  NativeCompareBlock.frame 208 [some coin] [] [] [] (comparisonPairs candidate actual)
def comparisonResult (coin : Bool) (candidate actual : Tag) : Machine.Configuration × Nat :=
  NativeCompareBlock.result 208 250 [some coin] [] [] [] (comparisonPairs candidate actual)

theorem compare_locations (index : Fin 8) : NativeCompareBlock.Located code (208 + 5 * index.val) 250 := by
  fin_cases index <;> constructor <;> decide_cbv
theorem accept_location : NativeCompareBlock.HaltAt code 248 true := by constructor <;> decide_cbv
theorem reject_location : NativeCompareBlock.HaltAt code 250 false := by constructor <;> decide_cbv

theorem comparison_enter_checked (coin : Bool) (candidate actual : Tag) :
    NativeDeterministic.run code 1 (returned 207 coin (some candidate) actual) = some (comparisonStart coin candidate actual) := by
  simp only [comparisonStart, NativeCompareBlock.frame, RandomFunctionMACNativeCaller.Native.comparison_candidates,
    RandomFunctionMACNativeCaller.Native.comparison_actuals, returned, machineAt, memory, ResponseLoading.loaded,
    ResponseLoading.fromCells, RequestExport.packetTape, encodeTag, Machine.Binary.encode]
  repeat' optimized_native_step

theorem comparison_checked (coin : Bool) (candidate actual : Tag) :
    NativeDeterministic.finish code 34 (comparisonStart coin candidate actual) = some (comparisonResult coin candidate actual) := by
  have sites : ∀ index, index < (comparisonPairs candidate actual).length →
      NativeCompareBlock.Located code (208 + 5 * index) 250 := by
    intro index inside
    exact compare_locations ⟨index, by simpa only [RandomFunctionMACNativeCaller.Native.comparison_width] using inside⟩
  have accepting : NativeCompareBlock.HaltAt code (208 + 5 * (comparisonPairs candidate actual).length) true := by
    simpa only [RandomFunctionMACNativeCaller.Native.comparison_width] using accept_location
  simpa only [comparisonStart, comparisonResult, RandomFunctionMACNativeCaller.Native.comparison_width, Nat.reduceMul, Nat.reduceAdd] using
    NativeCompareBlock.checked code 208 250 [some coin] [] [] [] (comparisonPairs candidate actual) sites accepting reject_location

theorem comparison_full_checked (coin : Bool) (candidate actual : Tag) :
    NativeDeterministic.finish code 35 (returned 207 coin (some candidate) actual) =
      some ((comparisonResult coin candidate actual).1, 1 + (comparisonResult coin candidate actual).2) := by
  rw [show 35 = 1 + 34 by rfl, NativeDeterministic.finish_after_run code 1 34 _ _
    (comparison_enter_checked coin candidate actual), comparison_checked]
  rfl

theorem comparison_halts (coin : Bool) (candidate actual : Tag) :
    (comparisonResult coin candidate actual).1.halted = true ∧ 1 + (comparisonResult coin candidate actual).2 ≤ 35 := by
  obtain ⟨halted, time, _⟩ := NativeDeterministic.finish_spec code 35 _ _ _ (comparison_full_checked coin candidate actual)
  exact ⟨halted, time⟩

theorem comparison_decision (coin : Bool) (candidate actual : Tag) :
    (comparisonResult coin candidate actual).1.outputTape.current = some (decide (actual = candidate)) := by
  have encoded : encodeTag candidate = encodeTag actual ↔ actual = candidate := by
    constructor
    · intro same
      have decoded := congrArg decodeTag same
      simpa only [tag_roundtrip] using decoded.symm
    · intro same; rw [same]
  simpa only [comparisonResult, RandomFunctionMACNativeCaller.Native.comparison_candidates,
    RandomFunctionMACNativeCaller.Native.comparison_actuals, encoded] using
    NativeCompareBlock.decision 208 250 [some coin] [] [] [] (comparisonPairs candidate actual)

end Foundation.Symmetric.RandomFunctionMACNativeOptimized
