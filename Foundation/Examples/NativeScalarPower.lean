import Foundation.Crypto.Semantics.Machine.ScalarGeneratorPower
import Foundation.Crypto.Semantics.Machine.ReturnFramedPower
import Foundation.Constructions.ElGamal.PrimeOrderSavedScalarSampler

namespace Examples.NativeScalarPower

open Machine

/-- A retained accepted scalar is installed as the actual exponent; the
native power result and the same scalar-bearing request coexist on tape.
This small arithmetic check makes no hardness claim about the toy group. -/
example :
    ∃ target used,
      RunsFor ScalarGeneratorPower.program
        ({inputTape := {left := List.replicate 3 (some true) ++ none::
            (encodeSecurityParameter 0 ++ frame (Binary.encode 3 7 ++ Binary.encode 3 3 ++ Binary.encode 3 2)).reverse.map some},
          outputTape := {left := (Binary.encode 3 1).reverse.map some}} : Configuration)
        target used ∧ target.halted = true ∧
      target.inputTape.bits =
        encodeSecurityParameter 0 ++ frame (Binary.encode 3 7 ++ Binary.encode 3 1 ++ Binary.encode 3 2) ++ Binary.encode 3 2 := by
  obtain ⟨c, target, used, _, run, halted, _, _, _, _, bits⟩ :=
    ScalarGeneratorPower.runs_numbers 0 7 3 2 1 (by decide) (by decide)
      (by decide) (by decide) (by decide)
  exact ⟨target, used, run, halted, by simpa using bits⟩

end Examples.NativeScalarPower
