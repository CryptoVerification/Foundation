import Foundation.Constructions.Symmetric.RandomFunctionMACNativeStages
import Foundation.Crypto.Semantics.Oracle.NativeCompareBlock

/-! Universal native comparison/halting for the same MAC caller. The first
mismatch may stop early; padding is applied only after the genuine halt.
All memory, response bits, private oracle state and trace are retained.
-/
namespace Foundation.Symmetric.RandomFunctionMACNativeCaller.Native
open Foundation.Probability CryptoOracle CryptoOracle.Interactive TimedExecution Machine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def comparisonPairs (candidate actual : Tag) := (encodeTag candidate).zip (encodeTag actual)

@[simp] theorem comparison_width (candidate actual : Tag) : (comparisonPairs candidate actual).length = 8 := by
  simp [comparisonPairs]

@[simp] theorem comparison_candidates (candidate actual : Tag) :
    (comparisonPairs candidate actual).map Prod.fst = encodeTag candidate := by
  apply List.map_fst_zip
  simp

@[simp] theorem comparison_actuals (candidate actual : Tag) :
    (comparisonPairs candidate actual).map Prod.snd = encodeTag actual := by
  apply List.map_snd_zip
  simp

def comparisonStart (coin : Bool) (candidate actual : Tag) : Machine.Configuration :=
  NativeCompareBlock.frame 207 [some coin] [] [] [] (comparisonPairs candidate actual)

def comparisonResult (coin : Bool) (candidate actual : Tag) : Machine.Configuration × Nat :=
  NativeCompareBlock.result 207 249 [some coin] [] [] [] (comparisonPairs candidate actual)

theorem compare_locations (index : Fin 8) : NativeCompareBlock.Located code (207 + 5 * index.val) 249 := by
  fin_cases index <;> constructor <;> decide_cbv

theorem accept_location : NativeCompareBlock.HaltAt code 247 true := by constructor <;> decide_cbv
theorem reject_location : NativeCompareBlock.HaltAt code 249 false := by constructor <;> decide_cbv

theorem comparison_enter_checked (coin : Bool) (candidate actual : Tag) :
    NativeDeterministic.run code 1 (returned 206 coin (some candidate) actual) =
      some (comparisonStart coin candidate actual) := by
  simp only [comparisonStart, NativeCompareBlock.frame, comparison_candidates, comparison_actuals,
    returned, machineAt, memory, ResponseLoading.loaded, ResponseLoading.fromCells,
    RequestExport.packetTape, encodeTag, Machine.Binary.encode]
  repeat' mac_native_step

theorem comparison_checked (coin : Bool) (candidate actual : Tag) :
    NativeDeterministic.finish code 34 (comparisonStart coin candidate actual) =
      some (comparisonResult coin candidate actual) := by
  have sites : ∀ index, index < (comparisonPairs candidate actual).length →
      NativeCompareBlock.Located code (207 + 5 * index) 249 := by
    intro index inside
    exact compare_locations ⟨index, by simpa only [comparison_width] using inside⟩
  have accepting : NativeCompareBlock.HaltAt code (207 + 5 * (comparisonPairs candidate actual).length) true := by
    simpa only [comparison_width] using accept_location
  simpa only [comparisonStart, comparisonResult, comparison_width, Nat.reduceMul, Nat.reduceAdd] using
    NativeCompareBlock.checked code 207 249 [some coin] [] [] [] (comparisonPairs candidate actual)
      sites accepting reject_location

theorem comparison_full_checked (coin : Bool) (candidate actual : Tag) :
    NativeDeterministic.finish code 35 (returned 206 coin (some candidate) actual) =
      some ((comparisonResult coin candidate actual).1, 1 + (comparisonResult coin candidate actual).2) := by
  rw [show 35 = 1 + 34 by rfl, NativeDeterministic.finish_after_run code 1 34 _ _
    (comparison_enter_checked coin candidate actual), comparison_checked]
  rfl

theorem comparison_halts (coin : Bool) (candidate actual : Tag) :
    (comparisonResult coin candidate actual).1.halted = true ∧
      1 + (comparisonResult coin candidate actual).2 ≤ 35 := by
  obtain ⟨halted, time, _⟩ := NativeDeterministic.finish_spec code 35 _ _ _
    (comparison_full_checked coin candidate actual)
  exact ⟨halted, time⟩

theorem comparison_decision (coin : Bool) (candidate actual : Tag) :
    (comparisonResult coin candidate actual).1.outputTape.current = some (decide (actual = candidate)) := by
  have encoded : encodeTag candidate = encodeTag actual ↔ actual = candidate := by
    constructor
    · intro same
      have decoded := congrArg decodeTag same
      simpa only [tag_roundtrip] using decoded.symm
    · intro same; rw [same]
  simpa only [comparisonResult, comparison_candidates, comparison_actuals, encoded] using
    NativeCompareBlock.decision 207 249 [some coin] [] [] [] (comparisonPairs candidate actual)

/-- This is a bound for every pair of tags, not a finite selection of test
values. Surplus time pads only the halted native configuration. -/
theorem comparison_run {State : Type} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (coin : Bool) (candidate actual : Tag)
    (horizon : Nat) (enough : 35 ≤ horizon) :
    TimedExecution.eval (Reification.timedStep code oracle) horizon
      (⟨state, .running (returned 206 coin (some candidate) actual), trace⟩ : Configuration State) =
      PMF.pure ⟨state, .running (comparisonResult coin candidate actual).1, trace⟩ :=
  NativeDeterministic.finish_timed code oracle state trace 35 _ _ _
    (comparison_full_checked coin candidate actual) horizon ((comparison_halts coin candidate actual).2.trans enough)

end Foundation.Symmetric.RandomFunctionMACNativeCaller.Native
