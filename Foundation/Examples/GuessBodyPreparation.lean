import Foundation.Crypto.Semantics.Machine.GuessBodyPreparation
import Foundation.Constructions.ElGamal.MachineRepresented

namespace Machine.Examples

/-- The native body's physical cells agree with the actual represented
ElGamal guess-request code, including the raw final product field. -/
example {α : Type} (E : FiniteBitEncoding α) (y product : α)
    (before padding beforeOutput : List (Option Bool)) (n : Nat)
    (instanceBits first last reply message₀ message₁ state selected : List Bool) :
    (prepareGuessBodyFinish before padding beforeOutput n instanceBits first (E.encode y) last reply
      message₀ message₁ state selected (E.encode product)).outputTape.left =
      ((ElGamal.requestCodeOfElement E).encode (.inr (state, (y, product)))).reverse.map some ++ none :: beforeOutput := by
  rw [prepareGuessBodyFinish_output]
  simp [ElGamal.requestCodeOfElement, FiniteBitEncoding.sum, FiniteBitEncoding.prod,
    FiniteBitEncoding.bitstring, List.append_assoc]

/-- Empty state and empty product still require both delimiters. A false
payload bit inside the first ciphertext field is copied as data. -/
example (before padding beforeOutput : List (Option Bool)) :
    (prepareGuessBodyFinish before padding beforeOutput 2 [false] [true] [false] [true]
      [false] [] [true] [] [] []).outputTape.left =
      [some false, some false, some true, some false, some true] ++ none :: beforeOutput := by
  rw [prepareGuessBodyFinish_output]
  rfl

/-- Empty selected-message and product blocks can precede arbitrary caller
cells. The delimiter writer must stop at the state separator, not at a
false payload bit, and must retain those following cells exactly. -/
example (beforeInput beforeOutput tail : List (Option Bool)) :
    evalConfigWithin writeDelimited
      (writeDelimitedContextStart beforeInput beforeOutput (none :: tail) [false, true] 6)
      (writeDelimitedSteps [false, true]) =
      PMF.pure (writeDelimitedContextFinish beforeInput beforeOutput (none :: tail) [false, true] 6) :=
  writeDelimitedContext_eval _ _ _ _ _

/-- The complete finite continuation runs from the physical post-arithmetic
layout. This checks simultaneous composition of state restoration, tuple
scanning, delimiter copying, four stored-block scans and product copying. -/
example (before padding beforeOutput : List (Option Bool)) :
    evalConfigWithin prepareGuessBody
      (prepareGuessBodyStart before padding beforeOutput 2 [false] [true] [false] [true]
        [false] [true, false] [false, true] [false, false, true] [true, false] [false, true])
      (prepareGuessBodySteps 2 [false] [true] [false] [true]
        [false] [true, false] [false, true] [false, false, true] [true, false] [false, true]) =
      PMF.pure (prepareGuessBodyFinish before padding beforeOutput 2 [false] [true] [false] [true]
        [false] [true, false] [false, true] [false, false, true] [true, false] [false, true]) :=
  prepareGuessBody_eval _ _ _ _ _ _ _ _ _ _ _ _ _ _

example (n : Nat) (instanceBits first second last reply message₀ message₁ state selected product : List Bool) :
    prepareGuessBodySteps n instanceBits first second last reply message₀ message₁ state selected product ≤
      5*n + 14*instanceBits.length + 18*first.length + 24*second.length + 10*last.length +
        5*reply.length + 18*(message₀.length + message₁.length) + 15*state.length +
        5*selected.length + 8*product.length + 127 :=
  prepareGuessBody_steps_le _ _ _ _ _ _ _ _ _ _ _

example : prepareGuessBody.length = 174 := prepareGuessBody_length

end Machine.Examples
