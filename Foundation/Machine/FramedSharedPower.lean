import Foundation.Machine.FramedSharedPowerInput
import Foundation.Machine.BinaryPowerExternalWidth
import Foundation.Machine.NativeInvocation

namespace Machine.FramedSharedPower

/-- Guarded native exponentiation after physically assembling the public
request's generator, scalar and modulus. The complete request remains on
the input tape, and the resulting group element is returned above it. -/
def program : Program := FramedSharedPowerInput.program.followedBy
  (GuardedCompiler.rawCompileOpposite BinaryPowerExternalWidth.program)

theorem runs_valid (n : Nat) (modulus exponent generator publicKey message firstComponent : List Bool)
    (hModulus : modulus.length = n+3)
    (hExponent : exponent.length = modulus.length)
    (hGenerator : generator.length = modulus.length)
    (hKey : publicKey.length = modulus.length)
    (result : List Bool)
    (correct : evalWithin BinaryPowerExternalWidth.program
      (BinaryColumnSlotFill.fullSlots publicKey exponent modulus)
      (BinaryPowerExternalWidth.budget (BinaryColumnSlotFill.fullSlots publicKey exponent modulus).length) =
        PMF.pure (some result)) :
    let raw := encodeSecurityParameter n ++ frame (modulus++exponent++generator++publicKey++message) ++ firstComponent
    let columns := BinaryColumnSlotFill.fullSlots publicKey exponent modulus
    ∃ c target used,
      used ≤ FramedExponentPreparation.validBudget n modulus exponent (generator++publicKey++message) +
        8*columns.length+6*generator.length+9*publicKey.length+3*(message++firstComponent).length+61 +
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
  let raw := encodeSecurityParameter n ++ frame (modulus++exponent++generator++publicKey++message) ++ firstComponent
  let columns := BinaryColumnSlotFill.fullSlots publicKey exponent modulus
  let saved := none::raw.reverse.map some
  obtain ⟨prepared, u, hu, preparation, halt, input, output⟩ :=
    FramedSharedPowerInput.runs_valid n modulus exponent generator publicKey message firstComponent hModulus hExponent hGenerator hKey
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
  change used ≤ FramedExponentPreparation.validBudget n modulus exponent (generator++publicKey++message) +
      8*columns.length+6*generator.length+9*publicKey.length+3*(message++firstComponent).length+61+
        GuardedCompiler.rawTraceBudget BinaryPowerExternalWidth.budget columns.length
  change u ≤ FramedExponentPreparation.validBudget n modulus exponent (generator++publicKey++message) +
    8*columns.length+6*generator.length+9*publicKey.length+3*(message++firstComponent).length+60 at hu
  omega

theorem runs_numbers (n modulus exponent generator publicKey message : Nat)
    (firstComponent : List Bool) (hOne : 1 < modulus) (hModulus : modulus < 2^(n+3))
    (hExponent : exponent < 2^(n+3)) (hKey : publicKey < modulus) :
    let p := Binary.encode (n+3) modulus
    let s := Binary.encode (n+3) exponent
    let g := Binary.encode (n+3) generator
    let h := Binary.encode (n+3) publicKey
    let m := Binary.encode (n+3) message
    let raw := encodeSecurityParameter n ++ frame (p++s++g++h++m) ++ firstComponent
    let columns := BinaryColumnSlotFill.fullSlots h s p
    ∃ c target used,
      used ≤ FramedExponentPreparation.validBudget n p s (g++h++m)+8*columns.length+
        6*g.length+9*h.length+3*(m++firstComponent).length+61+
          GuardedCompiler.rawTraceBudget BinaryPowerExternalWidth.budget columns.length ∧
      RunsFor program (Configuration.initial raw) target used ∧ target.halted = true ∧
      c.halted = true ∧ c.outputBits = Binary.encode (n+3) (publicKey^exponent % modulus) ∧
      target.inputTape.Equivalent
        ((GuardedCompiler.rawResultFrom BinaryPowerExternalWidth.program columns [none]
          (none::raw.reverse.map some) c).swapTapes).inputTape ∧
      target.outputTape.Equivalent
        ((GuardedCompiler.rawResultFrom BinaryPowerExternalWidth.program columns [none]
          (none::raw.reverse.map some) c).swapTapes).outputTape := by
  dsimp only
  apply runs_valid n _ _ _ _ _ firstComponent (by simp) (by simp) (by simp) (by simp)
  exact BinaryPowerExternalWidth.eval_numbers (n+3) modulus publicKey exponent hOne
    hKey hExponent hModulus

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _ FramedSharedPowerInput.no_randomBit
    (GuardedCompiler.rawCompileOpposite_no_randomBit _ BinaryPowerExternalWidth.no_randomBit) tape

end Machine.FramedSharedPower
