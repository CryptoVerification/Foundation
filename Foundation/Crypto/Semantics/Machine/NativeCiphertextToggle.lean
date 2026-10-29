import Foundation.Crypto.Semantics.Machine.NativeUniformSequence

/-! An explicit caller reads the preceding ciphertext cell and replaces its bit
by its complement, keeping private input and every other output cell. -/
namespace Machine.NativeCiphertextToggle
open Foundation.Probability NativeUniformSequence

def code : Program :=
  [.moveLeft .output, .branch .output 7 2 4,
   .write .output true, .jump 6, .write .output false, .jump 6,
   .moveRight .output, .halt]

theorem run (input output : Tape) (ciphertext : Bool) :
    evalConfigWithin code
      (NativeBitChoice.start input {output with left := some ciphertext :: output.left}) 6 =
      PMF.pure {pc := 7, inputTape := input, outputTape := {output with left := some (!ciphertext) :: output.left}, halted := true} := by
  cases ciphertext <;> simp [code, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
    Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.tape,
    Tape.moveLeft, Tape.moveRight, Tape.write]

theorem stops : StopsEverywhere code 6 := by
  intro input output finish trace
  have h := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  cases hl : output.left with
  | nil =>
    have he : evalConfigWithin code (NativeBitChoice.start input output) 6 =
        PMF.pure {pc := 7, inputTape := input, outputTape := output.moveLeft, halted := true} := by
      simp [code, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
        Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.tape,
        Tape.moveLeft, hl]
    rw [he, PMF.mem_support_pure_iff] at h
    subst finish
    rfl
  | cons bit rest =>
    cases bit with
    | none =>
      have he : evalConfigWithin code (NativeBitChoice.start input output) 6 =
          PMF.pure {pc := 7, inputTape := input, outputTape := output.moveLeft, halted := true} := by
        simp [code, evalConfigWithin, stepPMF, next, NativeBitChoice.start,
          Instruction.next, Configuration.updateTape, Configuration.advance, Configuration.tape,
          Tape.moveLeft, hl]
      rw [he, PMF.mem_support_pure_iff] at h
      subst finish
      rfl
    | some bit =>
      have he := run input {output with left := rest} bit
      have ho' : ({{output with left := rest} with left := some bit :: rest} : Tape) = output := by
        cases output; simp_all
      rw [ho'] at he
      rw [he, PMF.mem_support_pure_iff] at h
      subst finish
      rfl

end Machine.NativeCiphertextToggle
