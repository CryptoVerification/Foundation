import Foundation.Machine.MultiplyOperandPreparation
import Foundation.Machine.StoredCallPreparation

namespace Machine

/-- Saved cells just before the raw final DDH component. This is a layout
specification for existing encoded input, not a machine instruction. -/
def multiplyCallBeforeElement (before : List (Option Bool)) (n : Nat)
    (instanceBits first second last : List Bool) : List (Option Bool) :=
  (FiniteBitEncoding.delimit second).reverse.map some ++
    (FiniteBitEncoding.delimit first).reverse.map some ++
    (encodeSecurityParameter (FiniteBitEncoding.delimit first ++ FiniteBitEncoding.delimit second ++ last).length).reverse.map some ++
    (encodeSecurityParameter n ++ frame instanceBits).reverse.map some ++ none :: before

/-- The completed operand preparation is the actual input to the native
call preparation. All four retained blocks and both sets of represented
blank padding occur in this equality of full configurations. -/
theorem prepareMultiplyOperandsFinish_call_layout (before savedOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply canonical selected : List Bool) (blanks : Nat) :
    (prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none)
      n instanceBits first second last reply canonical selected).resumeAt 0 =
      prepareStoredCallStart (multiplyCallBeforeElement before n instanceBits first second last)
        (none :: selected.reverse.map some ++ none :: savedOutput) last reply canonical selected
        (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last)
        blanks (instanceBits.length + 1 - (2 * last.length + 1)) := by
  have hInput := prepareMultiplyOperandsFinish_input before savedOutput (List.replicate blanks none)
    n instanceBits first second last reply canonical selected
  have hOutput := prepareMultiplyOperandsFinish_output before savedOutput (List.replicate blanks none)
    n instanceBits first second last reply canonical selected
  change ({
    inputTape := (prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none)
      n instanceBits first second last reply canonical selected).inputTape
    outputTape := (prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none)
      n instanceBits first second last reply canonical selected).outputTape } : Configuration) = _
  rw [hInput, hOutput]
  simp [prepareStoredCallStart, seekBitstringNextStart_layout, multiplyCallBeforeElement, List.append_assoc]

/-- Charge the frontier scans and request rewind on the actual returned
arithmetic operand configuration. No request bits are supplied again by a
fresh initial-configuration operation. -/
theorem prepareMultiplyOperandsFinish_call_eval (before savedOutput : List (Option Bool))
    (n : Nat) (instanceBits first second last reply canonical selected : List Bool) (blanks : Nat) :
    evalConfigWithin prepareStoredCall
      ((prepareMultiplyOperandsFinish before savedOutput (List.replicate blanks none)
        n instanceBits first second last reply canonical selected).resumeAt 0)
      (prepareStoredCallSteps last reply canonical selected
        (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last)) =
      PMF.pure (prepareStoredCallFinish (multiplyCallBeforeElement before n instanceBits first second last)
        (none :: selected.reverse.map some ++ none :: savedOutput) last reply canonical selected
        (encodeSecurityParameter n ++ frame instanceBits ++ frame selected ++ frame last)
        blanks (instanceBits.length + 1 - (2 * last.length + 1))) := by
  rw [prepareMultiplyOperandsFinish_call_layout]
  exact prepareStoredCall_eval _ _ _ _ _ _ _ _ _

end Machine
