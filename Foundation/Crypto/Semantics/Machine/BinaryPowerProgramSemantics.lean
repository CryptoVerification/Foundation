import Foundation.Crypto.Semantics.Machine.BinaryPowerProgram
import Foundation.Crypto.Semantics.Machine.BinaryPowerSemantics
import Foundation.Crypto.Semantics.Machine.BinaryPowerSeedSemantics

set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace Machine.BinaryPowerProgramSemantics

open BinaryProductSelection BinaryProductSemantics

/-- The complete finite square-and-multiply machine computes fixed-width
modular exponentiation. Every write, call, rewind and final output copy is
part of `BinaryPowerProgram.program`; this theorem is its evaluator law. -/
theorem eval_power_encoded (columns : List BinaryModularAddition.Column)
    (hNonempty : columns ≠ [])
    (hOne : 1 < Binary.value (columns.map Prod.snd))
    (hOperand : Binary.value (columns.map fun c => c.1.1) < Binary.value (columns.map Prod.snd))
    (hRoom : 2 * Binary.value (columns.map Prod.snd) ≤ 2 ^ columns.length) :
    evalWithin BinaryPowerProgram.program (BinaryModularAddition.interleave columns)
      (BinaryPowerProgram.budget (BinaryModularAddition.interleave columns).length) =
      PMF.pure (some (Binary.encode columns.length
        (Binary.value (columns.map fun c => c.1.1) ^
          Binary.value (columns.map fun c => c.1.2) %
          Binary.value (columns.map Prod.snd)))) := by
  let input := BinaryModularAddition.interleave columns
  let initialized : Configuration :=
    { pc := 116, inputTape := { left := input.reverse.map some },
      outputTape := { left := (BinaryProductInitialization.matrix columns).reverse.map some }, halted := true }
  have hEval : evalConfigWithin BinaryProductInitialization.program (Configuration.initial input)
      (17 * columns.length + 2) = PMF.pure initialized := by
    have emptyStart : BinaryProductInitialization.initializationStart [] [] input = Configuration.initial input := by
      cases input <;> rfl
    have h := BinaryProductInitialization.eval_interleave_context columns [] []
    change evalConfigWithin _ (BinaryProductInitialization.initializationStart [] [] input) _ = _ at h
    rw [emptyStart] at h
    simpa only [List.append_nil] using h
  have hPad : evalConfigWithin BinaryProductInitialization.program (Configuration.initial input)
      (17 * (input.length + 1)) = PMF.pure initialized := by
    rw [evalConfigWithin_eq_of_le _ _ (17 * columns.length + 2) _
      (by simp only [input, interleave_length]; omega)]
    · exact hEval
    · intro target trace
      have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
      rw [hEval, PMF.mem_support_pure_iff] at member
      exact member ▸ rfl
  let seeded := BinaryPowerSeed.seeded (initialColumns columns)
  have hWidth : seeded.length = columns.length := by simp [seeded, initialColumns]
  have hAcc : Binary.value (seeded.map Column.accumulator) = 1 :=
    BinaryPowerSeedSemantics.seeded_initial_accumulator columns hNonempty
  have hMod : seeded.map Column.modulus = columns.map Prod.snd :=
    BinaryPowerSeedSemantics.seeded_initial_modulus columns
  have hOp : seeded.map Column.operand = columns.map fun c => c.1.1 :=
    BinaryPowerSeedSemantics.seeded_initial_operand columns
  have hRemaining : remainingBits seeded = columns.map fun c => c.1.2 :=
    BinaryPowerSeedSemantics.seeded_initial_remaining columns
  obtain ⟨finalColumns, finalSaved, loopTarget, loopSteps, hFinalWidth, hLoopBound,
    loopRun, hLoopHalt, hLoopInput, hLoopOutput, hValue⟩ :=
    BinaryPowerSemantics.runs_correct seeded (input.reverse.map some)
      (by rw [hAcc, hMod]; exact hOne)
      (by simpa only [hOp, hMod] using hOperand)
      (by simpa only [hMod, hWidth] using hRoom)
  obtain ⟨target, used, hUsed, native, hHalt, hOutput, _⟩ :=
    BinaryPowerProgram.runs_from_components BinaryPowerLoop.program BinaryPowerLoop.entry_in_range
      input columns initialized
      (by simp only [input, interleave_length]; omega) rfl rfl rfl hPad
      finalColumns finalSaved loopTarget loopSteps hFinalWidth hLoopBound
      loopRun hLoopHalt hLoopInput hLoopOutput
  have hBits : finalColumns.map Column.accumulator = Binary.encode columns.length
      (Binary.value (columns.map fun c => c.1.1) ^
        Binary.value (columns.map fun c => c.1.2) % Binary.value (columns.map Prod.snd)) := by
    have he := Binary.encode_value (finalColumns.map Column.accumulator)
    rw [List.length_map, hFinalWidth, hWidth, hValue, hMod, hOp, hAcc, hRemaining,
      ← Nat.mod_eq_of_lt hOne, BinaryPowerSemantics.finishValue_one,
      BinaryPowerSemantics.power_value] at he
    exact he.symm
  have halts : HaltsWith BinaryPowerProgram.program input
      (Binary.encode columns.length
        (Binary.value (columns.map fun c => c.1.1) ^
          Binary.value (columns.map fun c => c.1.2) % Binary.value (columns.map Prod.snd))) used :=
    ⟨target, native, hHalt, hOutput.trans hBits⟩
  exact (evalWithin_eq_of_haltsWithin _ input used _
    (halts.haltsWithin_of_no_randomBit BinaryPowerProgram.no_randomBit)
    (BinaryPowerProgram.haltsWithin input)).symm.trans
      (halts.evalWithin_eq_pure_of_no_randomBit BinaryPowerProgram.no_randomBit)

end Machine.BinaryPowerProgramSemantics
