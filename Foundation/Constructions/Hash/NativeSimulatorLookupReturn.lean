import Foundation.Constructions.Hash.NativeSimulatorLookup
import Foundation.Crypto.Semantics.Oracle.HaltReturn

/-! Compile the actual sequential lookup's final native halt into a jump
into an arbitrary continuation. Both successful and missing lookups retain
all physical tape cells, external state and transcript. -/
namespace Foundation.Hash.Native.SimulatorLookup
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

theorem lookupFinish_halt_instruction {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) :
    (lookupCode n κ)[(lookupFinish query table beforeInput beforeOutput).pc]? = some (.native .halt) := by
  induction table generalizing beforeInput with
  | nil => exact missing_halt_instruction n κ
  | cons entry rest ih =>
      simp only [lookupFinish]
      split_ifs
      · exact found_halt_instruction n κ
      · exact ih _

/-- The source lookup occupies its original addresses; its two actual halt
instructions become jumps into the relocated continuation. -/
def lookupHost (n κ : Nat) (body : Code) : Code := HaltReturn.host (lookupCode n κ) body

theorem lookupHost_length (n κ : Nat) (body : Code) :
    (lookupHost n κ body).length = 78 + 10 * n + 2 * κ + body.length := by
  simp [lookupHost, HaltReturn.host_length, lookupCode_length]

/-- No host resume or table normalization occurs at this call boundary.
The resumeAt on the right describes the state produced by an actual jump. -/
theorem lookup_return_run {State : Type*} {n κ : Nat} (body : Code)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (lookupHost n κ body) oracle) (lookupSteps query table)
      (NativeCode.frame state trace (scanStart table query beforeInput beforeOutput)) =
      PMF.pure (NativeCode.frame state trace
        ((lookupFinish query table beforeInput beforeOutput).resumeAt (lookupCode n κ).length)) := by
  have prefixRun := lookup_stage_run oracle state trace query table beforeInput beforeOutput false
  simp only [Bool.toNat_false, Nat.add_zero] at prefixRun
  have h := HaltReturn.return_run (lookupCode n κ) body oracle state trace
    (scanStart table query beforeInput beforeOutput)
    { lookupFinish query table beforeInput beforeOutput with halted := false }
    (lookupSteps query table - 1) rfl prefixRun
    (lookupFinish_halt_instruction query table beforeInput beforeOutput)
  have positive := lookupSteps_positive query table
  simpa only [lookupHost, show lookupSteps query table - 1 + 1 = lookupSteps query table by omega,
    Machine.Configuration.resumeAt] using h

/-- An absent key visits every entry, so its exact runtime is independent
of the values and of the order of the nonmatching keys. -/
theorem lookupSteps_missing {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (fresh : table.lookup query = none) :
    lookupSteps query table = table.length * (9 * n + 8 * κ + 18) + n + κ + 5 := by
  induction table with
  | nil => simp [lookupSteps]
  | cons entry rest ih =>
      by_cases equalKey : entry.1 = query
      · simp [equalKey] at fresh
      · rcases entry with ⟨key, value⟩
        have reverseUnequal : query ≠ key := Ne.symm equalKey
        have restFresh : rest.lookup query = none := by
          simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr reverseUnequal,
            Bool.false_eq_true, ↓reduceIte] using fresh
        simp only [lookupSteps, equalKey, ↓reduceIte, List.length_cons, ih restFresh]
        ring

theorem lookup_return_targets {State : Type*} {n κ : Nat} (body : Code) (returnAt : Nat → Nat)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) :
    TimedExecution.eval (Reification.timedStep (HaltReturn.hostWithReturns (lookupCode n κ) body returnAt) oracle)
      (lookupSteps query table) (NativeCode.frame state trace (scanStart table query beforeInput beforeOutput)) =
      PMF.pure (NativeCode.frame state trace ((lookupFinish query table beforeInput beforeOutput).resumeAt
        (returnAt (lookupFinish query table beforeInput beforeOutput).pc))) := by
  have prefixRun := lookup_stage_run oracle state trace query table beforeInput beforeOutput false
  simp only [Bool.toNat_false, Nat.add_zero] at prefixRun
  have h := HaltReturn.return_run_with_targets (lookupCode n κ) body returnAt oracle state trace
    (scanStart table query beforeInput beforeOutput)
    { lookupFinish query table beforeInput beforeOutput with halted := false }
    (lookupSteps query table - 1) rfl prefixRun
    (lookupFinish_halt_instruction query table beforeInput beforeOutput)
  have positive := lookupSteps_positive query table
  simpa only [show lookupSteps query table - 1 + 1 = lookupSteps query table by omega,
    Machine.Configuration.resumeAt] using h

/-- The runtime exit address records exactly which branch the original
lookup reached; no host-side decision is executed by the compiled code. -/
theorem lookupFinish_pc {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) :
    (lookupFinish query table beforeInput beforeOutput).pc =
      if (table.lookup query).isSome then copyPc n κ + 7 * n else missingPc n κ + (n + κ + 1) + 2 := by
  induction table generalizing beforeInput with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      by_cases equalKey : key = query
      · simp [lookupFinish, equalKey, foundFinish]
      · have reverseUnequal : query ≠ key := Ne.symm equalKey
        simp only [lookupFinish, equalKey, ↓reduceIte, List.lookup_cons,
          beq_eq_false_iff_ne.mpr reverseUnequal]
        exact ih _

end Foundation.Hash.Native.SimulatorLookup
