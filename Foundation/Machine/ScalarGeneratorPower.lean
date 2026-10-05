import Foundation.Machine.ScalarGeneratorPowerRequest
import Foundation.Machine.FramedGeneratorPower

namespace Machine.ScalarGeneratorPower

/-- Continue an accepted scalar on the retained tapes through installation
of the exponent and guarded modular exponentiation. The same sampled scalar
is retained in the request beneath the actual power-result cells. -/
def program : Program := ScalarGeneratorPowerRequest.program.followedBy FramedGeneratorPower.program

theorem runs_numbers (n modulus order generator scalar : Nat)
    (hOne : 1 < modulus) (hModulus : modulus < 2^(n+3))
    (hOrder : order < 2^(n+3)) (hScalar : scalar < 2^(n+3)) (hGenerator : generator < modulus) :
    let p := Binary.encode (n+3) modulus
    let q := Binary.encode (n+3) order
    let g := Binary.encode (n+3) generator
    let s := Binary.encode (n+3) scalar
    let raw := encodeSecurityParameter n ++ frame (p++q++g)
    let modified := encodeSecurityParameter n ++ frame (p++s++g)
    let columns := BinaryColumnSlotFill.fullSlots g s p
    ∃ c target used,
      used ≤ 20*raw.length+40*(n+3)+100 +
        FramedExponentPreparation.validBudget n p s g + 4*columns.length+8*g.length+32+
          GuardedCompiler.rawTraceBudget BinaryPowerExternalWidth.budget columns.length ∧
      RunsFor program
        ({inputTape := {left := List.replicate (n+3) (some true) ++ none::raw.reverse.map some},
          outputTape := {left := s.reverse.map some}} : Configuration) target used ∧
      target.halted = true ∧ c.halted = true ∧
      c.outputBits = Binary.encode (n+3) (generator^scalar % modulus) ∧
      target.inputTape.Equivalent
        ((GuardedCompiler.rawResultFrom BinaryPowerExternalWidth.program columns [none]
          (none::modified.reverse.map some) c).swapTapes).inputTape ∧
      target.outputTape.Equivalent
        ((GuardedCompiler.rawResultFrom BinaryPowerExternalWidth.program columns [none]
          (none::modified.reverse.map some) c).swapTapes).outputTape ∧
      target.inputTape.bits = modified ++ Binary.encode (n+3) (generator^scalar % modulus) := by
  dsimp only
  let p := Binary.encode (n+3) modulus
  let q := Binary.encode (n+3) order
  let g := Binary.encode (n+3) generator
  let s := Binary.encode (n+3) scalar
  let raw := encodeSecurityParameter n ++ frame (p++q++g)
  let modified := encodeSecurityParameter n ++ frame (p++s++g)
  let columns := BinaryColumnSlotFill.fullSlots g s p
  obtain ⟨installed, u, hu, installRun, installHalt, installInput, installOutput⟩ :=
    ScalarGeneratorPowerRequest.runs n p q g s (by simp [p]) (by simp [p,q])
      (by simp [p,g]) (by simp [p,s])
  obtain ⟨c, powered, v, hv, powerRun, powerHalt, coreHalt, coreBits, powerInput, powerOutput⟩ :=
    FramedGeneratorPower.runs_numbers n modulus scalar generator hOne hModulus hScalar hGenerator
  have layout : (Configuration.initial modified).Equivalent (installed.resumeAt 0) :=
    ⟨rfl, rfl, installInput.symm, installOutput.symm⟩
  obtain ⟨target, used, bound, run, halt, input, output⟩ :=
    installRun.followedBy_equivalent powerRun layout (Nat.zero_le _) rfl installHalt powerHalt
  have targetInput := input.symm.trans powerInput
  have targetOutput := output.symm.trans powerOutput
  have rawBits := GuardedCompiler.rawCompileOpposite_result_bits BinaryPowerExternalWidth.program
    columns [none] (none::modified.reverse.map some) c
  have retainedBits : target.inputTape.bits = modified ++ Binary.encode (n+3) (generator^scalar % modulus) := by
    rw [targetInput.bits, rawBits, coreBits]
    simp
  refine ⟨c, target, used, ?_, run, halt, coreHalt, coreBits, targetInput, targetOutput, retainedBits⟩
  change u ≤ 20*raw.length+40*(n+3)+100 at hu
  change v ≤ FramedExponentPreparation.validBudget n p s g +4*columns.length+8*g.length+31+
    GuardedCompiler.rawTraceBudget BinaryPowerExternalWidth.budget columns.length at hv
  change used ≤ 20*raw.length+40*(n+3)+100 +
    FramedExponentPreparation.validBudget n p s g +4*columns.length+8*g.length+32+
      GuardedCompiler.rawTraceBudget BinaryPowerExternalWidth.budget columns.length
  omega

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _ ScalarGeneratorPowerRequest.no_randomBit FramedGeneratorPower.no_randomBit tape

end Machine.ScalarGeneratorPower
