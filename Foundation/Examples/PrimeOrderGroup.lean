import Foundation.Constructions.ElGamal.PrimeOrderArithmetic
import Foundation.Constructions.ElGamal.PrimeOrderChooseNormalization

namespace ElGamal.PrimeOrderExamples

/-- A regression instance of the general prime-order subgroup construction.
No cryptographic hardness is asserted for this small group. -/
def generatorSeven : (ZMod 7)ˣ := ⟨2, 4, by decide, by decide⟩

def parametersSeven : PrimeOrderParameters 0 where
  modulus := 7
  scalarOrder := 3
  modulus_prime := by decide
  scalarOrder_prime := by decide
  generator := generatorSeven
  generator_order := by
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    apply orderOf_eq_prime
    · apply Units.ext; decide
    · intro h
      have hv := congrArg Units.val h
      have hn := congrArg ZMod.val hv
      exact (by decide : (2 : Nat) ≠ 1) hn
  modulus_lt := by decide

example : parametersSeven.scalarOrder < parametersSeven.modulus :=
  parametersSeven.scalarOrder_lt_modulus

example : (parametersSeven.scalarCode.encode ⟨2, by decide⟩) = [false, true, false] := rfl

example : parametersSeven.elementCode.decode
    (parametersSeven.elementCode.encode parametersSeven.parameters.generator) =
      some parametersSeven.parameters.generator :=
  parametersSeven.elementCode.decode_encode _

example :
    (concreteInstance parametersSeven.parameters parametersSeven.finiteAlgebra
      (groupDecrypt parametersSeven.parameters)).scheme.Correct :=
  parametersSeven.scheme_correct

example : (PrimeOrderParameters.instanceCode 0).encode parametersSeven =
    [true, true, true, true, true, false, false, true, false] := rfl

example : (PrimeOrderParameters.instanceCode 0).decode
    ((PrimeOrderParameters.instanceCode 0).encode parametersSeven) = some parametersSeven :=
  (PrimeOrderParameters.instanceCode 0).decode_encode _

example : parametersSeven.generator ^ parametersSeven.scalarOrder = 1 :=
  (parametersSeven.mem_subgroup_iff _).mp (Subgroup.mem_zpowers _)

/-- The same verified parameter record inhabits the represented interface's
domain. The lift adds no serialized field and no unproved decryptor. -/
private def representedSeven : PrimeOrderRepresentation.Domain 0 := ⟨parametersSeven⟩

example : ((PrimeOrderRepresentation.embed 0 representedSeven).toElGamalInstance).scheme.Correct :=
  PrimeOrderRepresentation.embed_correct 0 representedSeven

example : (PrimeOrderRepresentation.instanceCode 0).encode representedSeven =
    [true, true, true, true, true, false, false, true, false] := rfl

example : (PrimeOrderRepresentation.instanceCode 0).decode
    ((PrimeOrderRepresentation.instanceCode 0).encode representedSeven) = some representedSeven :=
  (PrimeOrderRepresentation.instanceCode 0).decode_encode _

/-- Both delimited choose fields are checked against the copied nine-bit
instance code by one fixed finite program. -/
example (state : List Bool) :
    let first := [false, true, false]
    let second := [true, false, false]
    let reply := Machine.canonicalMessageBits first second state
    let raw := Machine.encodeSecurityParameter 0 ++
      Machine.frame ((PrimeOrderRepresentation.instanceCode 0).encode representedSeven) ++
        Machine.frame reply
    (Machine.evalConfigWithin Machine.ChooseTwoWidthsPrefix.program
      (Machine.Configuration.initial raw)
      (Machine.ChooseTwoWidthsPrefix.budget raw.length)).map
        (fun c => c.outputTape.current) = PMF.pure (some true) := by
  simpa using PrimeOrderRepresentation.chooseTwoWidthsPrefix_eval 0 representedSeven
    [false, true, false] [true, false, false] state

example (state : List Bool) :
    let first := [false, true]
    let second := [true, false, false]
    let reply := Machine.canonicalMessageBits first second state
    let raw := Machine.encodeSecurityParameter 0 ++
      Machine.frame ((PrimeOrderRepresentation.instanceCode 0).encode representedSeven) ++
        Machine.frame reply
    (Machine.evalConfigWithin Machine.ChooseTwoWidthsPrefix.program
      (Machine.Configuration.initial raw)
      (Machine.ChooseTwoWidthsPrefix.budget raw.length)).map
        (fun c => c.outputTape.current) = PMF.pure (some false) := by
  simpa using PrimeOrderRepresentation.chooseTwoWidthsPrefix_eval 0 representedSeven
    [false, true] [true, false, false] state

/-- The rejection sampler's decoded limit distribution is this instance's
ideal scalar sampling law. Expected stopping remains distinct from the
simulator's every-branch stopping requirement. -/
example :
    let q := representedSeven.down.scalarOrder
    let code := Machine.Binary.fin q q.bits.length
      (by simpa using (Machine.Binary.value_lt q.bits).le)
    (Machine.evalLimit Machine.RejectionSampling.program q.bits
      (Machine.RejectionSampling.expectedPolynomialTime.almostSureHalts q.bits)).map code.decode =
      ((PrimeOrderRepresentation.embed 0 representedSeven).algebra.sampling.sampleScalar).map some :=
  PrimeOrderRepresentation.scalarSampler_exact 0 representedSeven

/-- The same finite binary multiplier computes the represented group product
on an assembled raw triple for this regression instance. -/
example (a b : (PrimeOrderRepresentation.embed 0 representedSeven).params.Element) :
    let C := representedSeven.down
    let raw := Machine.BinaryModularAddition.interleave
      (Machine.BinaryProductExternalWidth.numberColumns 3
        C.modulus a.val.val.val b.val.val.val)
    Machine.evalWithin Machine.BinaryProductExternalWidth.program raw
      (Machine.BinaryProductExternalWidth.budget raw.length) =
      PMF.pure (some ((PrimeOrderRepresentation.elementCode 0 representedSeven).encode
        ((PrimeOrderRepresentation.embed 0 representedSeven).params.mul a b))) :=
  PrimeOrderRepresentation.rawMultiply_correct 0 representedSeven a b

/-- The raw finite-bit power program computes the represented group power.
This does not yet parse a framed simulator request. -/
example (a : (PrimeOrderRepresentation.embed 0 representedSeven).params.Element)
    (s : (PrimeOrderRepresentation.embed 0 representedSeven).params.Scalar) :
    let C := representedSeven.down
    let raw := Machine.BinaryModularAddition.interleave
      (Machine.BinaryProductExternalWidth.numberColumns 3
        C.modulus a.val.val.val s.val)
    Machine.evalWithin Machine.BinaryPowerExternalWidth.program raw
      (Machine.BinaryPowerExternalWidth.budget raw.length) =
      PMF.pure (some ((PrimeOrderRepresentation.elementCode 0 representedSeven).encode
        ((PrimeOrderRepresentation.embed 0 representedSeven).params.power a s))) :=
  PrimeOrderRepresentation.rawPower_correct 0 representedSeven a s

/-- On the accepted branch, this actual framed-output code preserves every
state bit. Acceptance is still the enclosing normalizer's decision. -/
example (state : List Bool) :
    let generator := [false, true, false]
    let reply := Machine.canonicalMessageBits generator generator state
    let raw := Machine.encodeSecurityParameter 0 ++
      Machine.frame ((PrimeOrderRepresentation.instanceCode 0).encode representedSeven) ++
        Machine.frame reply
    Machine.evalWithin Machine.ChooseAcceptedOutput.program raw (10000*(raw.length+1)) =
      PMF.pure (some reply) :=
  Machine.ChooseAcceptedOutput.eval_valid 0
    ((PrimeOrderRepresentation.instanceCode 0).encode representedSeven) _

/-- The actual fallback code obtains `2` from the framed `p=7,q=3,g=2`
instance, emits it twice, and discards an arbitrary rejected reply. It does
not receive the generator as a preinstalled scratch tape. -/
example (reply : List Bool) :
    let raw := Machine.encodeSecurityParameter 0 ++
      Machine.frame ((PrimeOrderRepresentation.instanceCode 0).encode representedSeven) ++
        Machine.frame reply
    Machine.evalWithin Machine.FramedChooseDefaultOutput.program raw
      (10000000000000*(raw.length+1)) =
      PMF.pure (some (Machine.canonicalMessageBits [false, true, false] [false, true, false] [])) := by
  have h := Machine.FramedChooseDefaultOutput.eval_valid 0
    (Machine.Binary.encode 3 7) (Machine.Binary.encode 3 3) (Machine.Binary.encode 3 2) reply
    (Machine.Binary.encode_length _ _) (by simp) (by simp)
  have hInstance : (PrimeOrderRepresentation.instanceCode 0).encode representedSeven =
      Machine.Binary.encode 3 7 ++ Machine.Binary.encode 3 3 ++ Machine.Binary.encode 3 2 := rfl
  have hGenerator : Machine.Binary.encode 3 2 = [false, true, false] := rfl
  dsimp only
  rw [hInstance, ← hGenerator]
  exact h

end ElGamal.PrimeOrderExamples
