import Foundation.Constructions.ElGamal.PrimeOrderLogic
import Foundation.Crypto.Semantics.Machine.ReifyCompactProgram

namespace ElGamal.PrimeOrderRepresentation

open Machine

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Fixed normalizer code, retained as shared certified blocks. -/
def compactNormalizer : CompactProgram ChooseSafeValidation.program := by
  compact_program

/-- Fixed multiplication code, without expanding its guarded blocks. -/
def compactMultiplier : CompactProgram FramedProductSafeMultiply.program := by
  compact_program

/-- The same concrete compiler, applied to a shared source representation.
The explicit source program remains only in the type and erased certificates. -/
@[macro_inline] def compactCompile {source : Program} (code : CompactProgram source) :
    CompactProgram (logicCompiler.run source) := by
  compact_program [compactNormalizer, compactMultiplier]

/-- Full concrete code for an empty source, useful for exact size diagnostics. -/
def compactEmptyCode : CompactProgram (logicCompiler.run []) :=
  compactCompile (CompactProgram.literal [])

theorem compactCompile_length {source : Program} (code : CompactProgram source) :
    (compactCompile code).length = 136 * code.length +
      68 * compactNormalizer.length + 68 * compactMultiplier.length + 1764 := by
  rw [(compactCompile code).length_eq,
    logicCompiler, ProgramCompiler.run, ProgramCompiler.run,
    ProgramCompiler.run_chooseChallenge]
  rw [GuardedCompiler.chooseChallengeGuessCompile_length,
    ← code.length_eq, ← compactNormalizer.length_eq, ← compactMultiplier.length_eq]
  omega

/-- Every instruction of the shared output is the exact instruction emitted by
logical extraction. No approximation or different simulator is introduced. -/
theorem compactCompile_lookup {source : Program} (code : CompactProgram source) (pc : Nat) :
    (compactCompile code).lookup pc = (logicCompiler.run source)[pc]? :=
  (compactCompile code).lookup_eq pc

end ElGamal.PrimeOrderRepresentation
