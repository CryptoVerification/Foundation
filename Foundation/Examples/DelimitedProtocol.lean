import Foundation.Machine.DelimitedInput
import Foundation.Machine.DelimitedOutput
import Foundation.Machine.FramedOutput
import Foundation.Constructions.ElGamal.MachineRepresented

namespace Machine.Examples

/-- Valid empty data and an unterminated field have different status bits. -/
example : evalWithin readDelimited [false] 9 = PMF.pure (some [true]) :=
  readDelimited_evalWithin _

example : evalWithin readDelimited [] 5 = PMF.pure (some [false]) :=
  readDelimited_evalWithin _

/-- Only one data bit was complete before the final dangling prefix.
The partial payload is retained, followed by an explicit failure status. -/
example : evalWithin readDelimited [true, false, true] 17 =
    PMF.pure (some [false, false]) := readDelimited_evalWithin _

example : readDelimitedSteps [true, false, true, true, false] = 20 := rfl
example : writeDelimitedSteps [false, true] = 19 := rfl
example : writeDelimited.length = 14 := rfl
example : readDelimited.length = 16 := rfl

example : evalWithin writeDelimited [false, true] 20 =
    PMF.pure (some [true, false, true, true, false]) := writeDelimited_evalWithin _

/-- The current cryptographic protocol's nested product field can be
parsed with the native routine. The old response tag and the next message
and state stay on the input tape; the parser copies only the first element's
raw code. This is an invocation postcondition, not yet the entire simulator. -/
example {α : Type} (E : FiniteBitEncoding α) (m₀ m₁ : α) (state : List Bool) :
    evalConfigWithin readDelimited
      (readDelimitedStart [some false] []
        (FiniteBitEncoding.delimit (E.encode m₀) ++
          FiniteBitEncoding.delimit (E.encode m₁) ++ state))
      (readDelimitedSteps (FiniteBitEncoding.delimit (E.encode m₀) ++
        FiniteBitEncoding.delimit (E.encode m₁) ++ state)) =
      PMF.pure ({
        pc := 12,
        inputTape := { Tape.ofBits (FiniteBitEncoding.delimit (E.encode m₁) ++ state) with
          left := (FiniteBitEncoding.delimit (E.encode m₀)).reverse.map some ++ [some false] },
        outputTape := { left := some true :: (E.encode m₀).reverse.map some },
        halted := true } : Configuration) := by
  simpa [readDelimitedFinish, scanDelimited_complete] using
    readDelimited_eval [some false] []
      (FiniteBitEncoding.delimit (E.encode m₀) ++
        (FiniteBitEncoding.delimit (E.encode m₁) ++ state))

/-- Caller code outside these native routines may be randomized. Their
exact returning configuration laws preserve saved data and the status bit. -/
example (pre suffix : Program) (returnPc : Nat)
    (beforeInput beforeOutput : List (Option Bool)) (bits : List Bool) :
    evalConfigWithin (Program.withSubroutine pre readDelimited suffix returnPc)
      ((readDelimitedStart beforeInput beforeOutput bits).rebasePc pre.length)
      (readDelimitedSteps bits) =
      PMF.pure ((readDelimitedFinish beforeInput beforeOutput bits).resumeAt returnPc) :=
  readDelimited_withSubroutine_eval _ _ _ _ _ _

example (pre suffix : Program) (returnPc : Nat)
    (beforeInput beforeOutput : List (Option Bool)) (bits : List Bool) :
    evalConfigWithin (Program.withSubroutine pre writeDelimited suffix returnPc)
      ((writeDelimitedStart beforeInput beforeOutput bits).rebasePc pre.length)
      (writeDelimitedSteps bits) =
      PMF.pure ((writeDelimitedFinish beforeInput beforeOutput bits).resumeAt returnPc) :=
  writeDelimited_withSubroutine_eval _ _ _ _ _ _

example : PolynomialTime readDelimited := readDelimited_polynomialTime
example : PolynomialTime writeDelimited := writeDelimited_polynomialTime
example : PolynomialTime writeFrame := writeFrame_polynomialTime

/-- Unary-length framing used by operation inputs is a different format
from the nested product delimiter. Both now have native writing routines. -/
example : writeFrameSteps [false, true] = 36 := rfl
example : writeFrame.length = 24 := rfl
example : evalWithin writeFrame [false, true] 37 =
    PMF.pure (some [true, true, false, false, true]) := writeFrame_evalWithin _
example : evalWithin writeFrame [] 11 = PMF.pure (some [false]) := writeFrame_evalWithin _

example (pre suffix : Program) (returnPc : Nat) (bits : List Bool) :
    evalConfigWithin (Program.withSubroutine pre writeFrame suffix returnPc)
      ((Configuration.initial bits).rebasePc pre.length) (writeFrameSteps bits) =
      PMF.pure ((writeFrameFinish bits).resumeAt returnPc) :=
  writeFrame_withSubroutine_eval _ _ _ _

end Machine.Examples
