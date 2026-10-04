import Foundation.Constructions.ElGamal.Concrete
import Foundation.Notions.PKE.Correctness
import Mathlib.Algebra.Group.Basic

namespace ElGamal

open Foundation.Probability

/-- Additional algebra for decryption. The group supplies inverses and
cancellation; the two fields identify the construction's multiplication and
the shared secret. These laws are not inferred from `FiniteAlgebra` alone. -/
structure DecryptionAlgebra (params : DDHParameters) [Group params.Element] where
  mul_eq : ∀ a b, params.mul a b = a * b
  power_exchange : ∀ x y,
    params.power (params.power params.generator x) y =
      params.power (params.power params.generator y) x

/-- Commuting scalar multiplication, together with `power_mul`, suffices
for the shared-secret law. No commutative group instance is required. -/
theorem DecryptionAlgebra.of_scalar_mul_comm (params : DDHParameters)
    [Group params.Element] (L : FiniteAlgebra params)
    (hMul : ∀ a b, params.mul a b = a * b)
    (hComm : ∀ x y, params.mulScalar x y = params.mulScalar y x) :
    DecryptionAlgebra params where
  mul_eq := hMul
  power_exchange := by
    intro x y
    rw [L.power_mul, L.power_mul, hComm]

/-- ElGamal decryption `ζ / β^x`. This is a mathematical group operation;
no machine implementation or running-time bound is asserted here. -/
def groupDecrypt (params : DDHParameters) [Group params.Element]
    (sk : params.Scalar) (ct : params.Element × params.Element) :
    Option params.Element :=
  some (ct.2 / params.power ct.1 sk)

theorem groupDecrypt_encrypt (params : DDHParameters) [Group params.Element]
    (D : DecryptionAlgebra params) (m : params.Element) (x r : params.Scalar) :
    groupDecrypt params x
      (params.power params.generator r,
        params.mul m (params.power (params.power params.generator x) r)) =
      some m := by
  simp only [groupDecrypt, D.mul_eq, D.power_exchange x r]
  simp

/-- Perfect correctness of the same finite construction used by the
existing IND-CPA reduction, now with an actual group decryptor. -/
theorem concreteInstance_correct (params : DDHParameters) [Group params.Element]
    (L : FiniteAlgebra params) (D : DecryptionAlgebra params) :
    (concreteInstance params L (groupDecrypt params)).scheme.Correct := by
  intro m pk sk ct hKey hCipher
  change (pk, sk) ∈ (L.sampling.sampleScalar.map
    (fun x => (params.power params.generator x, x))).support at hKey
  obtain ⟨x, _, hKey⟩ := (PMF.mem_support_map_iff ..).mp hKey
  have hpk : pk = params.power params.generator x := (congrArg Prod.fst hKey).symm
  have hsk : sk = x := (congrArg Prod.snd hKey).symm
  rw [hpk] at hCipher
  change ct ∈ (L.sampling.sampleScalar.map
    (fun r => (params.power params.generator r,
      params.mul m (params.power (params.power params.generator x) r)))).support at hCipher
  obtain ⟨r, _, hCipher⟩ := (PMF.mem_support_map_iff ..).mp hCipher
  rw [← hCipher, hsk]
  exact groupDecrypt_encrypt params D m x r

end ElGamal
