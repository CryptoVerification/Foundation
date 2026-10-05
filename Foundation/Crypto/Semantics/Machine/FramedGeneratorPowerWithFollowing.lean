import Foundation.Crypto.Semantics.Machine.FramedGeneratorPowerWithFollowingInput
import Foundation.Crypto.Semantics.Machine.BinaryPowerExternalWidth
import Foundation.Crypto.Semantics.Machine.NativeInvocation

namespace Machine.FramedGeneratorPowerWithFollowing

/-- Guarded native exponentiation after physically assembling the public
request's generator, scalar and modulus. The complete request remains on
the input tape, and the resulting group element is returned above it. -/
def program : Program := FramedGeneratorPowerWithFollowingInput.program.followedBy
  (GuardedCompiler.rawCompileOpposite BinaryPowerExternalWidth.program)

theorem runs_valid (n : Nat) (modulus exponent generator following : List Bool)
    (hModulus : modulus.length = n+3)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length)
    (result : List Bool)
    (correct : evalWithin BinaryPowerExternalWidth.program
      (BinaryColumnSlotFill.fullSlots generator exponent modulus)
      (BinaryPowerExternalWidth.budget (BinaryColumnSlotFill.fullSlots generator exponent modulus).length) =
        PMF.pure (some result)) :
    let raw := encodeSecurityParameter n ++ frame (modulus++exponent++generator++following)
    let columns := BinaryColumnSlotFill.fullSlots generator exponent modulus
    ∃ c target used,
      used ≤ FramedExponentPreparation.validBudget n modulus exponent (generator++following) +
        4*columns.length + 9*generator.length + 3*following.length + 41 +
          GuardedCompiler.rawTraceBudget BinaryPowerExternalWidth.budget columns.length ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      c.halted = true ∧ c.outputBits = result ∧
      target.inputTape.Equivalent
        ((GuardedCompiler.rawResultFrom BinaryPowerExternalWidth.program columns [none]
          (none::raw.reverse.map some) c).swapTapes).inputTape ∧
      target.outputTape.Equivalent
        ((GuardedCompiler.rawResultFrom BinaryPowerExternalWidth.program columns [none]
          (none::raw.reverse.map some) c).swapTapes).outputTape := by
  dsimp only
  let raw := encodeSecurityParameter n ++ frame (modulus++exponent++generator++following)
  let columns := BinaryColumnSlotFill.fullSlots generator exponent modulus
  let saved := none::raw.reverse.map some
  obtain ⟨prepared, u, hu, preparation, halt, input, output⟩ :=
    FramedGeneratorPowerWithFollowingInput.runs_valid n modulus exponent generator following hModulus hExponent hGenerator
  obtain ⟨c, coreHalt, coreBits, law⟩ := GuardedCompiler.rawCompileOpposite_result
    BinaryPowerExternalWidth.program columns result [none] saved BinaryPowerExternalWidth.budget
    BinaryPowerExternalWidth.no_randomBit (BinaryPowerExternalWidth.haltsWithin columns) correct
  let returned := (GuardedCompiler.rawResultFrom BinaryPowerExternalWidth.program columns [none] saved c).swapTapes
  have trace : PaddedRunsFor (GuardedCompiler.rawCompileOpposite BinaryPowerExternalWidth.program)
      (GuardedCompiler.packInputStart [none] saved columns).swapTapes returned
      (GuardedCompiler.rawTraceBudget BinaryPowerExternalWidth.budget columns.length) := by
    apply (mem_support_evalConfigWithin_iff _ _ _ _).mp
    rw [law]
    simp [returned]
  obtain ⟨v, hv, call⟩ := trace.toRunsFor_le
  have boundary : ({Tape.ofBits columns with left := [none]} : Tape).Equivalent (Tape.ofBits columns) := by
    refine ⟨rfl, ?_, fun _ => rfl⟩
    intro i
    cases columns <;> cases i <;> rfl
  have layout : (GuardedCompiler.packInputStart [none] saved columns).swapTapes.Equivalent
      (prepared.resumeAt 0) := by
    refine ⟨rfl, rfl, input.symm, ?_⟩
    exact boundary.trans output.symm
  obtain ⟨target, used, bound, run, halted, inputResult, outputResult⟩ :=
    preparation.followedBy_equivalent call layout (Nat.zero_le _) rfl halt rfl
  refine ⟨c, target, used, ?_, run, halted, coreHalt, coreBits, inputResult.symm, outputResult.symm⟩
  change used ≤ FramedExponentPreparation.validBudget n modulus exponent (generator++following) +
      4*columns.length+9*generator.length+3*following.length+41+
        GuardedCompiler.rawTraceBudget BinaryPowerExternalWidth.budget columns.length
  change u ≤ FramedExponentPreparation.validBudget n modulus exponent (generator++following) +
    4*columns.length+9*generator.length+3*following.length+40 at hu
  omega

theorem runs_numbers (n modulus exponent generator : Nat) (following : List Bool)
    (hOne : 1 < modulus) (hModulus : modulus < 2^(n+3))
    (hExponent : exponent < 2^(n+3)) (hGenerator : generator < modulus) :
    let modulusBits := Binary.encode (n+3) modulus
    let exponentBits := Binary.encode (n+3) exponent
    let generatorBits := Binary.encode (n+3) generator
    let raw := encodeSecurityParameter n ++ frame (modulusBits++exponentBits++generatorBits++following)
    let columns := BinaryColumnSlotFill.fullSlots generatorBits exponentBits modulusBits
    ∃ c target used,
      used ≤ FramedExponentPreparation.validBudget n modulusBits exponentBits (generatorBits++following) +
        4*columns.length+9*generatorBits.length+3*following.length+41+
          GuardedCompiler.rawTraceBudget BinaryPowerExternalWidth.budget columns.length ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      c.halted = true ∧ c.outputBits = Binary.encode (n+3) (generator^exponent % modulus) ∧
      target.inputTape.Equivalent
        ((GuardedCompiler.rawResultFrom BinaryPowerExternalWidth.program columns [none]
          (none::raw.reverse.map some) c).swapTapes).inputTape ∧
      target.outputTape.Equivalent
        ((GuardedCompiler.rawResultFrom BinaryPowerExternalWidth.program columns [none]
          (none::raw.reverse.map some) c).swapTapes).outputTape := by
  dsimp only
  apply runs_valid n _ _ _ following (by simp) (by simp) (by simp)
  exact BinaryPowerExternalWidth.eval_numbers (n+3) modulus generator exponent hOne
    hGenerator hExponent hModulus

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _ FramedGeneratorPowerWithFollowingInput.no_randomBit
    (GuardedCompiler.rawCompileOpposite_no_randomBit _ BinaryPowerExternalWidth.no_randomBit) tape

end Machine.FramedGeneratorPowerWithFollowing
