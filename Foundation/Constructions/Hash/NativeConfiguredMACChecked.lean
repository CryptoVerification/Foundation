import Foundation.Crypto.Semantics.Oracle.NativeCheckedRelocation
import Foundation.Examples.MixedCircuitMACLinkedGame

/-! Accepted traces for the actual linked caller, including the physical
analysis/head-restoration suffix. No terminal padding is used at a live
caller/server handoff. -/
namespace CryptoOracle.Interactive.NativeVerdictRestore
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false

theorem checked (mask : List Bool) (input output : Tape) :
    NativeDeterministic.run (code mask) (3 * mask.length + 4) (NativeVerdictPacket.start 0 input output) =
      some (finish mask input output) := by
  have firstRun := NativeDeterministic.run_return (NativeVerdictPacket.code mask) (rewind mask.length)
    (2 * mask.length + 3) (NativeVerdictPacket.start 0 input output) (NativeVerdictPacket.finish mask input output)
    rfl rfl (NativeVerdictPacket.checked mask input output)
  let before := (NativeVerdictPacket.code mask).map (HaltReturn.instruction (NativeVerdictPacket.code mask).length)
  have body := NativeDeterministic.run_relocated before (rewind mask.length) (mask.length + 1)
    (NativeVerdictPacket.start 0 input (NativeVerdictPacket.finish mask input output).outputTape)
    {pc := mask.length, inputTape := input, outputTape := (Tape.moveLeft^[mask.length]) (NativeVerdictPacket.finish mask input output).outputTape, halted := true}
    (rewind_checked mask.length input (NativeVerdictPacket.finish mask input output).outputTape)
  rw [show 3 * mask.length + 4 = (2 * mask.length + 3) + (mask.length + 1) by omega, NativeDeterministic.run_add]
  change ((NativeDeterministic.run (HaltReturn.host (NativeVerdictPacket.code mask) (rewind mask.length))
    (2 * mask.length + 3) _).bind _) = _
  rw [firstRun, Option.bind_some]
  simpa only [code, before, HaltReturn.host, CodeRelocation.host, List.length_map, NativeVerdictPacket.finish,
    NativeVerdictPacket.start, Machine.Configuration.resumeAt, Machine.Configuration.rebasePc,
    finish, restored, NativeVerdictPacket.result_length, Nat.add_zero] using body

end CryptoOracle.Interactive.NativeVerdictRestore

namespace Foundation.Hash.Native.ConfiguredMACChecked
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability Foundation.Symmetric
open RandomFunctionMACNativeCaller
set_option backward.isDefEq.respectTransparency false

abbrev callerCode (mask : List Bool) := RandomFunctionMACNativeOptimized.AnalysisLinked.linkedCode mask

theorem preserve (mask : List Bool) (count : Nat) (start final : Machine.Configuration)
    (checked : NativeDeterministic.run RandomFunctionMACNativeOptimized.code count start = some final)
    (active : final.halted = false) : NativeDeterministic.run (callerCode mask) count start = some final :=
  NativeDeterministic.run_preserved_active RandomFunctionMACNativeOptimized.code (NativeVerdictRestore.code mask) count start final checked active

theorem call_fetch (mask : List Bool) (pc : Nat)
    (fetched : RandomFunctionMACNativeOptimized.code[pc]? = some .call) : (callerCode mask)[pc]? = some .call := by
  have inside : pc < RandomFunctionMACNativeOptimized.code.length := List.getElem?_eq_some_iff.mp fetched |>.1
  rw [callerCode, RandomFunctionMACNativeOptimized.AnalysisLinked.linkedCode, HaltReturn.source_lookup _ _ pc inside, fetched]
  rfl

theorem first_checked (mask : List Bool) (coin : Bool) :
    NativeDeterministic.run (callerCode mask) 12 (Native.afterCoin coin) = some (Native.firstCall coin) :=
  preserve mask _ _ _ (RandomFunctionMACNativeOptimized.first_setup_checked coin) rfl

theorem second_checked (mask : List Bool) (coin : Bool) (first : Tag) :
    NativeDeterministic.run (callerCode mask) 12 (Native.returned 16 coin none first) =
      some (RandomFunctionMACNativeOptimized.secondCall coin first) :=
  preserve mask _ _ _ (RandomFunctionMACNativeOptimized.second_setup_checked coin first) rfl

theorem repeated_checked (mask : List Bool) (coin : Bool) (second : Tag) :
    NativeDeterministic.run (callerCode mask) ((if coin then 1 else 59) + 12) (Native.returned 31 coin none second) =
      some (RandomFunctionMACNativeOptimized.thirdCall coin (RandomFunctionMACNativeOptimized.savedSecond coin second) second) := by
  apply preserve mask _ _ _ _ rfl
  rw [NativeDeterministic.run_add, RandomFunctionMACNativeOptimized.select_second_checked, Option.bind_some,
    RandomFunctionMACNativeOptimized.third_setup_checked]

theorem verify_checked (mask : List Bool) (coin : Bool) (second repeated : Tag) :
    NativeDeterministic.run (callerCode mask) ((if coin then 59 else 1) + 10)
      (Native.returned 121 coin (RandomFunctionMACNativeOptimized.savedSecond coin second) repeated) =
      some (RandomFunctionMACNativeOptimized.lastCall coin (if coin then repeated else second) repeated) := by
  apply preserve mask _ _ _ _ rfl
  rw [NativeDeterministic.run_add, RandomFunctionMACNativeOptimized.select_candidate_checked, Option.bind_some,
    RandomFunctionMACNativeOptimized.last_setup_checked]

theorem initial_step {Source : Type} (mask : List Bool) (oracle : BitOracle Source) (state : Source)
    (trace : List (List Bool × List Bool)) :
    Reification.timedStep (callerCode mask) oracle (⟨state, .running {}, trace⟩ : Configuration Source) =
      sampleBit.map (fun coin => ⟨state, .running (Native.afterCoin coin), trace⟩) := by
  have first : (callerCode mask)[0]? = some (.native (.randomBit .input)) := by
    rw [callerCode, RandomFunctionMACNativeOptimized.AnalysisLinked.linkedCode,
      HaltReturn.source_lookup _ _ 0 (by rw [RandomFunctionMACNativeOptimized.code_length]; decide)]
    rfl
  simp [Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
    transition, first, Machine.Instruction.next, Machine.Configuration.updateTape, Machine.Configuration.advance,
    Native.afterCoin]
  congr 1
  funext coin
  cases coin <;> rfl

def finishMachine (mask : List Bool) (coin : Bool) (candidate actual : Tag) : Machine.Configuration :=
  (NativeVerdictRestore.finish mask
    (RandomFunctionMACNativeOptimized.comparisonResult coin candidate actual).1.inputTape
    (RandomFunctionMACNativeOptimized.comparisonResult coin candidate actual).1.outputTape).rebasePc RandomFunctionMACNativeOptimized.code.length

theorem finish_checked (mask : List Bool) (coin : Bool) (candidate actual : Tag) :
    NativeDeterministic.run (callerCode mask) ((1 + (RandomFunctionMACNativeOptimized.comparisonResult coin candidate actual).2) + (3 * mask.length + 4))
      (Native.returned 207 coin (some candidate) actual) = some (finishMachine mask coin candidate actual) := by
  have firstRun := NativeDeterministic.finish_return RandomFunctionMACNativeOptimized.code (NativeVerdictRestore.code mask)
    35 (Native.returned 207 coin (some candidate) actual) (RandomFunctionMACNativeOptimized.comparisonResult coin candidate actual).1
    (1 + (RandomFunctionMACNativeOptimized.comparisonResult coin candidate actual).2) rfl
    (RandomFunctionMACNativeOptimized.comparison_full_checked coin candidate actual)
  let before := RandomFunctionMACNativeOptimized.code.map (HaltReturn.instruction RandomFunctionMACNativeOptimized.code.length)
  have body := NativeDeterministic.run_relocated before (NativeVerdictRestore.code mask) (3 * mask.length + 4)
    (NativeVerdictPacket.start 0 (RandomFunctionMACNativeOptimized.comparisonResult coin candidate actual).1.inputTape
      (RandomFunctionMACNativeOptimized.comparisonResult coin candidate actual).1.outputTape)
    (NativeVerdictRestore.finish mask (RandomFunctionMACNativeOptimized.comparisonResult coin candidate actual).1.inputTape
      (RandomFunctionMACNativeOptimized.comparisonResult coin candidate actual).1.outputTape)
    (NativeVerdictRestore.checked ..)
  rw [NativeDeterministic.run_add]
  change ((NativeDeterministic.run (HaltReturn.host RandomFunctionMACNativeOptimized.code (NativeVerdictRestore.code mask)) _ _).bind _) = _
  rw [firstRun, Option.bind_some]
  simpa only [callerCode, RandomFunctionMACNativeOptimized.AnalysisLinked.linkedCode, before, HaltReturn.host,
    CodeRelocation.host, List.length_map, NativeVerdictPacket.start, Machine.Configuration.resumeAt,
    Machine.Configuration.rebasePc, Nat.add_zero, finishMachine] using body

end Foundation.Hash.Native.ConfiguredMACChecked
