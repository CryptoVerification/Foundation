import Foundation.Crypto.Semantics.Machine.ScalarGeneratorPowerWithFollowing
import Foundation.Crypto.Semantics.Machine.ReturnJoinedPower
import Foundation.Crypto.Semantics.Machine.NativeKeygenContinuation

namespace Machine.NativeEncryptionFirstPower

/-- Install one sampled scalar, calculate the first ciphertext component,
and retain the complete parameter/public-key/message request and that actual
component on the same input tape for the remaining encryption operations. -/
def program : Program := ScalarGeneratorPowerWithFollowing.program.followedBy ReturnJoinedPower.program

theorem runs_numbers (n modulus order generator scalar publicKey message : Nat)
    (hOne : 1 < modulus) (hModulus : modulus < 2^(n+3))
    (hOrder : order < 2^(n+3)) (hScalar : scalar < 2^(n+3)) (hGenerator : generator < modulus) :
    let p := Binary.encode (n+3) modulus
    let q := Binary.encode (n+3) order
    let g := Binary.encode (n+3) generator
    let s := Binary.encode (n+3) scalar
    let following := Binary.encode (n+3) publicKey ++ Binary.encode (n+3) message
    let raw := encodeSecurityParameter n ++ frame (p++q++g++following)
    let modified := encodeSecurityParameter n ++ frame (p++s++g++following)
    ∃ target used, used ≤ NativeKeygenContinuation.budget n ∧
      RunsFor program
        ({inputTape := {left := List.replicate (n+3) (some true) ++ none::raw.reverse.map some}, outputTape := {left := s.reverse.map some}} : Configuration) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent (Tape.ofBits (modified ++ Binary.encode (n+3) (generator^scalar % modulus))) ∧
      target.outputTape.Equivalent ({} : Tape) := by
  dsimp only
  let p := Binary.encode (n+3) modulus
  let q := Binary.encode (n+3) order
  let g := Binary.encode (n+3) generator
  let s := Binary.encode (n+3) scalar
  let following := Binary.encode (n+3) publicKey ++ Binary.encode (n+3) message
  let raw := encodeSecurityParameter n ++ frame (p++q++g++following)
  let modified := encodeSecurityParameter n ++ frame (p++s++g++following)
  let columns := BinaryColumnSlotFill.fullSlots g s p
  obtain ⟨c, powered, u, hu, powerRun, powerHalt, _, coreBits, powerInput, powerOutput, _⟩ :=
    ScalarGeneratorPowerWithFollowing.runs_numbers n modulus order generator scalar following
      hOne hModulus hOrder hScalar hGenerator
  have columnsLength : columns.length = 3*(n+3) := by
    simp [columns, BinaryColumnSlotFill.fullSlots_length, p, s, g]
  have rawLength : raw.length = n+10*(n+3)+2 := by
    simp [raw, p,q,g,following, frame, encodeSecurityParameter]; omega
  have modifiedLength : modified.length = n+10*(n+3)+2 := by
    simp [modified, p,s,g,following, frame, encodeSecurityParameter]; omega
  have hPowerLength : c.outputBits.length = n+3 := by rw [coreBits]; simp
  have hPowerBudget : u ≤ NativeKeygenContinuation.powerBudget n := by
    have validLength : FramedExponentPreparation.validBudget n p s (g++following) ≤ 300*(n+3) := by
      simp [FramedExponentPreparation.validBudget, BinaryThirdColumnTemplate.columns_length, p,s,g,following]
      omega
    change u ≤ 20*raw.length+40*(n+3)+100+
      FramedExponentPreparation.validBudget n p s (g++following)+4*columns.length+
      9*g.length+3*following.length+42+
        GuardedCompiler.rawTraceBudget BinaryPowerExternalWidth.budget columns.length at hu
    rw [rawLength, columnsLength] at hu
    have glen : g.length = n+3 := by simp [g]
    have flen : following.length = 2*(n+3) := by simp [following]; omega
    rw [glen, flen] at hu
    unfold NativeKeygenContinuation.powerBudget
    omega
  obtain ⟨joined, v, hv, joinRun, joinHalt, joinInput, joinOutput⟩ :=
    ReturnJoinedPower.runs BinaryPowerExternalWidth.program columns modified c
  have boundary : ((GuardedCompiler.rawResultFrom BinaryPowerExternalWidth.program columns [none]
      (none::modified.reverse.map some) c).swapTapes.resumeAt 0).Equivalent (powered.resumeAt 0) :=
    ⟨rfl, rfl, powerInput.symm, powerOutput.symm⟩
  obtain ⟨target, used, bound, run, halt, input, output⟩ :=
    powerRun.followedBy_equivalent joinRun boundary (Nat.zero_le _) rfl powerHalt joinHalt
  refine ⟨target, used, ?_, run, halt, ?_, output.symm.trans joinOutput⟩
  · have sourceStorage := NativeKeygenReturn.source_cells_le_of_run columns modified c powerRun powerOutput
    have startCells :
        ({inputTape := {left := List.replicate (n+3) (some true) ++ none::raw.reverse.map some}, outputTape := {left := s.reverse.map some}} : Configuration).inputTape.cells+
        ({inputTape := {left := List.replicate (n+3) (some true) ++ none::raw.reverse.map some}, outputTape := {left := s.reverse.map some}} : Configuration).outputTape.cells = raw.length+2*(n+3)+3 := by
      simp [Tape.cells, s]; omega
    rw [startCells, rawLength] at sourceStorage
    have returnBudget := ReturnJoinedPower.budget_le columns modified c
    rw [columnsLength, modifiedLength, hPowerLength] at returnBudget
    have limit : v ≤ 8*c.inputTape.cells+4*(3*(n+3))+2*(n+10*(n+3)+2)+40*(n+3)+100 := hv.trans returnBudget
    unfold NativeKeygenContinuation.budget
    omega
  · rw [coreBits] at joinInput
    exact input.symm.trans joinInput

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _ ScalarGeneratorPowerWithFollowing.no_randomBit
    ReturnJoinedPower.no_randomBit tape

end Machine.NativeEncryptionFirstPower
