import Foundation.Machine.RejectionSamplingSemantics

set_option maxRecDepth 4096

namespace Machine.Examples

open Foundation.Probability

/-- The parameterized code reads the binary modulus and has a certificate on
all raw bitstrings, not just encoded cryptographic requests. -/
example : ExpectedPolynomialTime RejectionSampling.program :=
  RejectionSampling.expectedPolynomialTime

example : ¬ PolynomialTime RejectionSampling.program := RejectionSampling.not_polynomialTime

example (input : List Bool) :
    expectedSteps RejectionSampling.program input ≤ (24 * (input.length + 1) : Nat) :=
  RejectionSampling.expectedSteps_le input

example (q : Nat) [NeZero q] :
    evalLimit RejectionSampling.program q.bits
      (RejectionSampling.expectedPolynomialTime.almostSureHalts q.bits) =
      (uniform (Fin q)).map (fun a => Binary.encode q.bits.length a.val) :=
  RejectionSampling.evalLimit_nat q

/-- Unit, odd-prime, and power-of-two boundary cases use the same finite code
and the proved limit semantics. -/
example : evalLimit RejectionSampling.program [true]
    (RejectionSampling.expectedPolynomialTime.almostSureHalts [true]) =
    PMF.pure [false] := RejectionSampling.evalLimit_one

example : evalLimit RejectionSampling.program (3 : Nat).bits
    (RejectionSampling.expectedPolynomialTime.almostSureHalts (3 : Nat).bits) =
    (uniform (Fin 3)).map (fun a => Binary.encode 2 a.val) :=
  RejectionSampling.evalLimit_nat 3

example : evalLimit RejectionSampling.program (4 : Nat).bits
    (RejectionSampling.expectedPolynomialTime.almostSureHalts (4 : Nat).bits) =
    (uniform (Fin 4)).map (fun a => Binary.encode 3 a.val) :=
  RejectionSampling.evalLimit_nat 4

example (q : Nat) [NeZero q] :
    let code := Binary.fin q q.bits.length (by simpa using (Binary.value_lt q.bits).le)
    (evalLimit RejectionSampling.program q.bits
      (RejectionSampling.expectedPolynomialTime.almostSureHalts q.bits)).map code.decode =
      (uniform (Fin q)).map some := RejectionSampling.evalLimit_nat_decoded q

/-- These bounded deterministic couplings test the actual parameterized
code; they do not claim that all random branches have this stopping bound. -/
private def inspect (input : List Bool) (steps : Nat) (bit : Bool) : Configuration :=
  runWithBits RejectionSampling.program (Configuration.initial input) steps (fun _ => bit)

example : (inspect [] 2 false).halted = true := by decide
example : (inspect [false] 5 false).halted = true := by decide
example : (inspect [true] 20 false).halted = true ∧
    (inspect [true] 20 false).outputBits = [false] := by decide
example : (inspect [true, true] 36 false).halted = true ∧
    (inspect [true, true] 36 false).outputBits = [false, false] := by decide
example : (inspect [true, true] 100 true).halted = false := by decide
example : (inspect [false, false, true] 44 false).halted = true ∧
    (inspect [false, false, true] 44 false).outputBits = [false, false, false] := by decide

example : HaltsWithin RejectionSampling.program [true] 5 := RejectionSampling.one_haltsWithin

example : evalWithin RejectionSampling.program [true] 5 = PMF.pure (some [false]) :=
  RejectionSampling.one_eval

end Machine.Examples
