import Foundation.Constructions.Hash.NativeSimulatorLookup
import Foundation.Crypto.Semantics.Machine.NativeBitstringRewind
import Foundation.Crypto.Semantics.Machine.NativeTraceTime
import Foundation.Crypto.Semantics.Oracle.NativeSubroutine

/-! Recover the actual physical table after a missing lookup using the
existing four-instruction native rewind. No host table reconstruction or
free removal of the retained outer blank is performed. -/
namespace Foundation.Hash.Native.SimulatorLookup
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false

/-- A failed search has traversed every original record without changing
its bits, and stopped at the original false end marker. -/
theorem lookupFinish_missing {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeInput beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) :
    lookupFinish query table beforeInput beforeOutput =
      missingFinish query ((table.flatMap entryBits).reverse.map some ++ beforeInput) beforeOutput := by
  induction table generalizing beforeInput with
  | nil => simp [lookupFinish]
  | cons entry rest ih =>
      by_cases equalKey : entry.1 = query
      · simp [equalKey] at fresh
      · rcases entry with ⟨key, value⟩
        have reverseUnequal : query ≠ key := Ne.symm equalKey
        have restFresh : rest.lookup query = none := by
          simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr reverseUnequal, Bool.false_eq_true, ↓reduceIte] using fresh
        simp only [lookupFinish, equalKey, ↓reduceIte]
        rw [ih _ restFresh]
        simp [List.reverse_append, List.map_append, List.append_assoc]

def rewindInput {n κ : Nat} (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool)) :
    NativeBitstringRewind.Input where
  bits := table.flatMap entryBits
  current := some false
  other := (missingFinish query [] beforeOutput).outputTape

theorem lookup_rewind_entry {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) :
    (lookupFinish query table [] beforeOutput).resumeAt 0 = NativeBitstringRewind.initial (rewindInput query table beforeOutput) := by
  rw [lookupFinish_missing query table [] beforeOutput fresh]
  simp [rewindInput, NativeBitstringRewind.initial, missingFinish, scanStart,
    tableBits, Tape.ofBits, Machine.Configuration.resumeAt]

/-- Exact physical rewind result: the extra left blank is retained. -/
theorem rewind_table_layout {n κ : Nat}
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) :
    (NativeBitstringRewind.finish (rewindInput query table beforeOutput)).inputTape =
      { Tape.ofBits (tableBits table) with left := [none] } := by
  simp only [NativeBitstringRewind.finish, rewindInput, tableBits]
  generalize table.flatMap entryBits = bits
  cases bits <;> simp [Tape.moveRight, Tape.ofBits, List.map_append]

/-- The returned time is the exact first halt, obtained from the existing
operational trace rather than from a padded horizon. -/
theorem rewind_first_joint {State : Type*} {n κ : Nat}
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) :
    runToBoundary (Reification.timedStep (NativeCode.code rewindBitstring) oracle)
      (fun frame => Reification.terminal frame.control) (2 * (table.flatMap entryBits).length + 4)
      (NativeCode.frame state trace ((lookupFinish query table [] beforeOutput).resumeAt 0)) =
      PMF.pure (NativeCode.frame state trace (NativeBitstringRewind.finish (rewindInput query table beforeOutput)),
        2 * (table.flatMap entryBits).length + 4) := by
  rw [lookup_rewind_entry query table beforeOutput fresh]
  have actual := rewindBitstring_runs_from (table.flatMap entryBits) (some false) []
    (missingFinish query [] beforeOutput).outputTape
  have costed := NativeBitstringRewind.component.firstArrival_costed_of_trace
    (rewindInput query table beforeOutput) _ _ actual rewindBitstring_no_randomBit rfl (Nat.le_refl _)
  have h := NativeCode.first_joint NativeBitstringRewind.component oracle state trace
    (rewindInput query table beforeOutput)
  rw [costed, PMF.pure_map] at h
  exact h

/-- Actual return into a finite continuation: the old halt is a native
jump. This theorem does not execute a host-side resume operation. -/
theorem rewind_first_return {State : Type*} {n κ : Nat}
    (tail : Code) (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (query : CompressionInput (Bits κ) (Bits n)) (table : CompressionTable (Bits κ) (Bits n))
    (beforeOutput : List (Option Bool)) (fresh : table.lookup query = none) :
    runToBoundary (Reification.timedStep (NativeCode.subroutinePrefix rewindBitstring ++ tail) oracle)
      (NativeCode.returnBoundary 5) (2 * (table.flatMap entryBits).length + 4)
      (NativeCode.frame state trace ((lookupFinish query table [] beforeOutput).resumeAt 0)) =
      PMF.pure (NativeCode.frame state trace
        ((NativeBitstringRewind.finish (rewindInput query table beforeOutput)).resumeAt 5),
        2 * (table.flatMap entryBits).length + 4) := by
  rw [lookup_rewind_entry query table beforeOutput fresh]
  have actual := rewindBitstring_runs_from (table.flatMap entryBits) (some false) []
    (missingFinish query [] beforeOutput).outputTape
  have costed := NativeBitstringRewind.component.firstArrival_costed_of_trace
    (rewindInput query table beforeOutput) _ _ actual rewindBitstring_no_randomBit rfl (Nat.le_refl _)
  have h := NativeCode.subroutine_first_joint NativeBitstringRewind.component tail oracle state trace
    (rewindInput query table beforeOutput)
  rw [costed, PMF.pure_map] at h
  exact h

end Foundation.Hash.Native.SimulatorLookup
