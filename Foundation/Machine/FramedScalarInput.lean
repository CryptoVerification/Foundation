import Foundation.Machine.FramedScalarPreparation
import Foundation.Machine.SavedBitstringRewind

namespace Machine.FramedScalarInput

/-- Prepare and physically rewind the scalar modulus, preserving its saved
width counter. The exact sampler can start at this returned input head. -/
def program : Program := FramedScalarPreparation.program.followedBy rewindBitstring

def validBudget (n : Nat) (modulus generator : List Bool) : Nat :=
  FramedScalarPreparation.validBudget n modulus generator + 2*(n+3)+5

theorem runs_valid (n : Nat) (modulus generator : List Bool) (q : Nat)
    (hWidth : modulus.length = n+3) (hPositive : q ≠ 0) (hFit : q < 2^(n+3)) :
    ∃ (target : Configuration) (used : Nat), used ≤ validBudget n modulus generator ∧
      RunsFor program (Configuration.initial
        (encodeSecurityParameter n ++ frame (modulus ++ Binary.encode (n+3) q ++ generator))) target used ∧
      target.halted = true ∧
      target.inputTape.Equivalent
        { Tape.ofBits q.bits with left := none :: List.replicate (n+3) (some true) } ∧
      target.outputTape.Equivalent ({} : Tape) := by
  obtain ⟨prepared, u, hu, prepRun, prepHalt, prepInput, prepOutput⟩ :=
    FramedScalarPreparation.runs_valid n modulus generator q hWidth hPositive hFit
  have rewindRun := rewindBitstring_runs_saved q.bits (List.replicate (n+3) (some true))
    none (List.replicate ((n+3)-q.bits.length) none) ({} : Tape)
  have layout :
      ({ inputTape := { left := q.bits.reverse.map some ++ none :: List.replicate (n+3) (some true), right := List.replicate ((n+3)-q.bits.length) none }
         outputTape := ({} : Tape) } : Configuration).Equivalent (prepared.resumeAt 0) :=
    ⟨rfl, rfl, prepInput.symm, prepOutput.symm⟩
  obtain ⟨target, used, hUsed, run, hHalt, hInput, hOutput⟩ :=
    prepRun.followedBy_equivalent rewindRun layout (Nat.zero_le _) rfl prepHalt rfl
  have hLength : q.bits.length ≤ n+3 := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hFit
  refine ⟨target, used, by unfold validBudget; omega, ?_, hHalt, ?_, hOutput.symm⟩
  · exact run
  · exact hInput.symm.trans (rewindBitstring_saved_input_equivalent q.bits
      (List.replicate (n+3) (some true)) ((n+3)-q.bits.length))

theorem validBudget_fixedWidth_polynomiallyBounded (modulus generator : Nat → Nat) :
    PolynomiallyBounded (fun n => validBudget n
      (Binary.encode (n+3) (modulus n)) (Binary.encode (n+3) (generator n))) := by
  exact ((FramedScalarPreparation.validBudget_fixedWidth_polynomiallyBounded modulus generator).add
    ((PolynomiallyBounded.const 2).mul
      (PolynomiallyBounded.id.add (PolynomiallyBounded.const 3)))).add (PolynomiallyBounded.const 5)

theorem no_randomBit (tape : TapeId) : Instruction.randomBit tape ∉ program :=
  Program.followedBy_no_randomBit _ _ FramedScalarPreparation.no_randomBit rewindBitstring_no_randomBit tape

end Machine.FramedScalarInput
