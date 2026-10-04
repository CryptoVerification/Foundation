import Foundation.Constructions.ElGamal.Correctness
import Foundation.Constructions.ElGamal.ConcreteReductionExamples
import Foundation.Constructions.ElGamal.MachineSecurity

namespace ElGamal.CorrectnessExamples

open Foundation.Probability
open ElGamal.ConcreteExamples ElGamal.ConcreteReductionExamples

/-- The group of two elements is used only to check algebra and probability
APIs. It is not a cryptographically hard DDH family. -/
@[instance_reducible] def bitGroup : Group Bool where
  mul := Bool.xor
  one := false
  inv := id
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one_mul := by intro a; cases a <;> rfl
  mul_one := by intro a; cases a <;> rfl
  inv_mul_cancel := by intro a; cases a <;> rfl

local instance : Group bitParams.Element := bitGroup

theorem bitDecryptionAlgebra : DecryptionAlgebra bitParams :=
  DecryptionAlgebra.of_scalar_mul_comm bitParams bitAlgebra
    (by intro a b; rfl)
    (by intro a b; cases a <;> cases b <;> rfl)

def correctBitDecrypt := groupDecrypt bitParams

noncomputable def correctBitInstance (n : Nat) : ConcreteInstance bitSamplingFamily n where
  params := bitParams
  algebra := bitAlgebra
  decrypt := correctBitDecrypt
  sampling_eq := by simp [bitSamplingFamily, bitAlgebra]

noncomputable def correctBitFamily : InstanceFamily (concreteINDCPAGoal bitSamplingFamily) :=
  correctBitInstance

theorem correctBitInstance_correct (n : Nat) :
    (correctBitInstance n).toElGamalInstance.scheme.Correct :=
  concreteInstance_correct bitParams bitAlgebra bitDecryptionAlgebra

/-- The old always-failing decryptor validates no decryption correctness,
although its IND-CPA advantage equality remains valid. -/
theorem bitDecrypt_not_correct :
    ¬ (concreteInstance bitParams bitAlgebra bitDecrypt).scheme.Correct := by
  intro hCorrect
  have hKey : (false, false) ∈
      (concreteInstance bitParams bitAlgebra bitDecrypt).scheme.keygen.support := by
    apply (PMF.mem_support_map_iff ..).mpr
    exact ⟨false, PMF.mem_support_uniformOfFintype false, rfl⟩
  have hCipher : (false, false) ∈
      ((concreteInstance bitParams bitAlgebra bitDecrypt).scheme.encrypt false false).support := by
    apply (PMF.mem_support_map_iff ..).mpr
    exact ⟨false, PMF.mem_support_uniformOfFintype false, rfl⟩
  have h := hCorrect false false false (false, false) hKey hCipher
  change (none : Option Bool) = some false at h
  contradiction

example (m x r : Bool) :
    correctBitDecrypt x (r, Bool.xor m (x && r)) = some m := by
  cases m <;> cases x <;> cases r <;> rfl

/-- The real decryptor uses the very same advantage equality as the old
syntax-only example. Correctness does not modify the IND-CPA reduction. -/
example (n : Nat)
    (A : INDCPAAdversary ProbComp (correctBitInstance n).toElGamalInstance.scheme) :
    concreteINDCPASemantics.advantage n (correctBitInstance n).toElGamalInstance.scheme A =
      (concreteDDHSemantics bitSamplingFamily).advantage n bitParams
        (ddhAdversaryOfINDCPA sampleBit (correctBitInstance n).toElGamalInstance A) :=
  concreteCompatibility_eq bitSamplingFamily n (correctBitInstance n) A

/-- Correctness and machine-class secrecy refer to the same represented
schemes. Group laws and the choice of decryptor discharge correctness;
machine primitives, normalization and DDH hardness discharge the existing
conditional secrecy theorem. No machine efficiency of decryption follows. -/
example
    (sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params))
    (X : Nat → Type 1) (embed : ∀ n, X n → ConcreteInstance sampling n)
    (groups : ∀ n x, Group (embed n x).params.Element)
    (algebra : ∀ n x, @DecryptionAlgebra (embed n x).params (groups n x))
    (decrypt_eq : ∀ n x, (embed n x).decrypt =
      @groupDecrypt (embed n x).params (groups n x))
    (M : RepresentedSimulatorPrimitives sampling X embed)
    (N : RepresentedChooseNormalizer M)
    (F : (n : Nat) → X n)
    (hDDH : SecureOnWithin (representedDDHGoal sampling X embed)
      (representedDDHInterface sampling X embed M.instanceCode
        (fun n x => (M.elementCode n x).triple)).pptClass
      ((representedReduction sampling X embed).mapFamily F)) :
    (∀ n, (embed n (F n)).toElGamalInstance.scheme.Correct) ∧
      SecureOnWithin (representedINDCPAGoal sampling X embed)
        (representedINDCPAElementPPTClass sampling X embed M.instanceCode M.elementCode) F := by
  constructor
  · intro n
    let _ := groups n (F n)
    change (concreteInstance (embed n (F n)).params (embed n (F n)).algebra
      (embed n (F n)).decrypt).scheme.Correct
    rw [decrypt_eq n (F n)]
    exact concreteInstance_correct _ _ (algebra n (F n))
  · exact secureRepresentedINDCPA_of_secureRepresentedDDH_nativeMachinePPT
      sampling X embed M N F hDDH

end ElGamal.CorrectnessExamples
