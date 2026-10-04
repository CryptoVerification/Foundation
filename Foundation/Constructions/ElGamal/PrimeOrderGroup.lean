import Foundation.Constructions.ElGamal.Correctness
import Foundation.Machine.BinaryEncoding
import Mathlib.FieldTheory.Finite.Basic

namespace ElGamal

/-- Public prime-order subgroup parameters of the finite field's unit group.
The modulus has an explicit binary width bound. Parameter generation and DDH
hardness are not inferred from these mathematical validity proofs. -/
structure PrimeOrderParameters (n : Nat) where
  modulus : Nat
  scalarOrder : Nat
  modulus_prime : modulus.Prime
  scalarOrder_prime : scalarOrder.Prime
  generator : (ZMod modulus)ˣ
  generator_order : orderOf generator = scalarOrder
  modulus_lt : modulus < 2 ^ (n + 3)

namespace PrimeOrderParameters

def subgroup {n : Nat} (C : PrimeOrderParameters n) := Subgroup.zpowers C.generator

theorem scalarOrder_lt_modulus {n : Nat} (C : PrimeOrderParameters n) :
    C.scalarOrder < C.modulus := by
  let : Fact C.modulus.Prime := ⟨C.modulus_prime⟩
  have h := orderOf_le_card_univ (x := C.generator)
  rw [C.generator_order, ZMod.card_units] at h
  have hp := C.modulus_prime.two_le
  omega

/-- Subgroup membership is precisely the modular `q`-th-root test. The
finite field's unit group is cyclic, and the generator already supplies
all `q` distinct roots. This theorem justifies the element decoder's test;
it does not provide an execution-time certificate for exponentiation. -/
theorem mem_subgroup_iff {n : Nat} (C : PrimeOrderParameters n)
    (a : (ZMod C.modulus)ˣ) : a ∈ C.subgroup ↔ a ^ C.scalarOrder = 1 := by
  classical
  let : Fact C.modulus.Prime := ⟨C.modulus_prime⟩
  let roots : Finset (ZMod C.modulus)ˣ :=
    Finset.univ.filter (fun x => x ^ C.scalarOrder = 1)
  let members : Finset (ZMod C.modulus)ˣ := (C.subgroup : Set _).toFinset
  have hSub : members ⊆ roots := by
    intro x hx
    have hx' : x ∈ C.subgroup := Set.mem_toFinset.mp hx
    have hPow := pow_card_eq_one (x := (⟨x, hx'⟩ : C.subgroup))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hCard : Fintype.card C.subgroup = C.scalarOrder := by
      rw [← Nat.card_eq_fintype_card]
      exact (Nat.card_zpowers C.generator).trans C.generator_order
    have := congrArg Subtype.val hPow
    simpa only [hCard, Subgroup.coe_pow, Subgroup.coe_one] using this
  have hMembers : members.card = C.scalarOrder := by
    change ((C.subgroup : Set (ZMod C.modulus)ˣ).toFinset).card = C.scalarOrder
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact (Nat.card_zpowers C.generator).trans C.generator_order
  have hRoots : roots.card ≤ C.scalarOrder :=
    IsCyclic.card_pow_eq_one_le C.scalarOrder_prime.pos
  have hEq : members = roots :=
    Finset.eq_of_subset_of_card_le hSub (hRoots.trans_eq hMembers.symm)
  change a ∈ C.subgroup ↔ _
  simpa [members, roots] using (congrArg (fun s => a ∈ s) hEq).to_iff

/-- The subgroup test can be stated entirely in terms of residue arithmetic.
Its implementation still has to account for every modular-power operation. -/
theorem mem_subgroup_iff_residue {n : Nat} (C : PrimeOrderParameters n)
    (a : (ZMod C.modulus)ˣ) :
    a ∈ C.subgroup ↔ a.val.val ^ C.scalarOrder % C.modulus = 1 := by
  let : Fact C.modulus.Prime := ⟨C.modulus_prime⟩
  have hVal : (a.val ^ C.scalarOrder).val = a.val.val ^ C.scalarOrder % C.modulus := by
    have hCast : ((a.val.val ^ C.scalarOrder : Nat) : ZMod C.modulus) =
        a.val ^ C.scalarOrder := by
      rw [Nat.cast_pow, ZMod.natCast_zmod_val]
    rw [← hCast, ZMod.val_natCast]
  rw [C.mem_subgroup_iff]
  constructor
  · intro h
    have hv := congrArg (fun u : (ZMod C.modulus)ˣ => u.val.val) h
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, hVal,
      ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt C.modulus_prime.one_lt] using hv
  · intro h
    apply Units.ext
    apply ZMod.val_injective
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, hVal,
      ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt C.modulus_prime.one_lt] using h

def parameters {n : Nat} (C : PrimeOrderParameters n) : DDHParameters where
  Element := C.subgroup
  Scalar := Fin C.scalarOrder
  generator := ⟨C.generator, Subgroup.mem_zpowers C.generator⟩
  power a x := a ^ x.val
  mulScalar x y := ⟨x.val * y.val % C.scalarOrder, Nat.mod_lt _ C.scalarOrder_prime.pos⟩
  mul a b := a * b

instance {n : Nat} (C : PrimeOrderParameters n) : Group C.parameters.Element :=
  inferInstanceAs (Group C.subgroup)

noncomputable def finiteAlgebra {n : Nat} (C : PrimeOrderParameters n) :
    FiniteAlgebra C.parameters where
  sampling :=
    { scalarFintype := inferInstanceAs (Fintype (Fin C.scalarOrder))
      scalarNonempty := ⟨⟨0, C.scalarOrder_prime.pos⟩⟩ }
  powerEquiv := (finCongr C.generator_order.symm).trans
    (finEquivZPowers (orderOf_pos_iff.mp (C.generator_order ▸ C.scalarOrder_prime.pos)))
  powerEquiv_apply := by
    intro x
    apply Subtype.ext
    rfl
  mulLeftEquiv := fun m => Equiv.mulLeft m
  mulLeftEquiv_apply := by intro m a; rfl
  power_mul := by
    intro x y
    apply Subtype.ext
    change (C.generator ^ x.val) ^ y.val = C.generator ^ (x.val * y.val % C.scalarOrder)
    rw [← pow_mul]
    simpa only [C.generator_order] using (pow_mod_orderOf C.generator (x.val * y.val)).symm

theorem decryptionAlgebra {n : Nat} (C : PrimeOrderParameters n) :
    DecryptionAlgebra C.parameters :=
  DecryptionAlgebra.of_scalar_mul_comm C.parameters C.finiteAlgebra
    (fun _ _ => rfl) (fun x y => by
      apply Fin.ext
      exact congrArg (fun k => k % C.scalarOrder) (Nat.mul_comm x.val y.val))

theorem scheme_correct {n : Nat} (C : PrimeOrderParameters n) :
    (concreteInstance C.parameters C.finiteAlgebra (groupDecrypt C.parameters)).scheme.Correct :=
  concreteInstance_correct C.parameters C.finiteAlgebra C.decryptionAlgebra

/-- Scalar values have a fixed width bounded by the security parameter. -/
def scalarCode {n : Nat} (C : PrimeOrderParameters n) :
    Machine.FiniteBitEncoding (Fin C.scalarOrder) :=
  Machine.Binary.fin C.scalarOrder (n + 3)
    (C.scalarOrder_lt_modulus.le.trans C.modulus_lt.le)

@[simp] theorem scalarCode_length {n : Nat} (C : PrimeOrderParameters n)
    (x : Fin C.scalarOrder) : (C.scalarCode.encode x).length = n + 3 :=
  Machine.Binary.fin_encode_length _ _ _ _

private noncomputable def unitOfResidue (p : Nat) (hp : p.Prime)
    (v : Nat) (hv : v < p ∧ v ≠ 0) : (ZMod p)ˣ := by
  let : Fact p.Prime := ⟨hp⟩
  exact Units.mk0 (v : ZMod p) (by
    intro hz
    have h := congrArg ZMod.val hz
    have h0 : v = 0 := by simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hv.1] using h
    exact hv.2 h0)

private theorem unitOfResidue_val (p : Nat) (hp : p.Prime)
    (v : Nat) (hv : v < p ∧ v ≠ 0) :
    (unitOfResidue p hp v hv).val = (v : ZMod p) := rfl

/-- Fixed-width field residues encode subgroup elements. The decoder checks
width, nonzero residue range, and subgroup membership. These are mathematical
checks; their bit-machine implementations are not inferred here. -/
noncomputable def elementCode {n : Nat} (C : PrimeOrderParameters n) :
    Machine.FiniteBitEncoding C.subgroup := by
  classical
  let : Fact C.modulus.Prime := ⟨C.modulus_prime⟩
  exact
    { encode := fun a => Machine.Binary.encode (n + 3) a.val.val.val
      decode := fun bits =>
        if bits.length = n + 3 then
          let v := Machine.Binary.value bits
          if hv : v < C.modulus ∧ v ≠ 0 then
            let a := unitOfResidue C.modulus C.modulus_prime v hv
            if hm : a ^ C.scalarOrder = 1 then
              some ⟨a, (C.mem_subgroup_iff a).mpr hm⟩ else none
          else none
        else none
      decode_encode := by
        intro a
        have hRange : a.val.val.val < C.modulus := ZMod.val_lt _
        have hNonzero : a.val.val.val ≠ 0 := by
          intro hz
          have hCast := ZMod.natCast_zmod_val a.val.val
          rw [hz, Nat.cast_zero] at hCast
          exact Units.ne_zero a.val hCast.symm
        have hUnit : unitOfResidue C.modulus C.modulus_prime a.val.val.val ⟨hRange, hNonzero⟩ = a.val := by
          apply Units.ext
          rw [unitOfResidue_val, ZMod.natCast_zmod_val]
        simp only [Machine.Binary.encode_length,
          Machine.Binary.value_encode (hRange.trans C.modulus_lt), ↓reduceIte]
        simp only [hRange]
        simp [hUnit, (C.mem_subgroup_iff a.val).mp a.property] }

theorem elementCode_decode_wrong_length {n : Nat} (C : PrimeOrderParameters n)
    (bits : List Bool) (h : bits.length ≠ n + 3) : C.elementCode.decode bits = none := by
  classical
  simp [elementCode, h]

@[simp] theorem elementCode_length {n : Nat} (C : PrimeOrderParameters n)
    (a : C.subgroup) : (C.elementCode.encode a).length = n + 3 :=
  Machine.Binary.encode_length _ _

/-- This identifies the represented group operation with the residue
arithmetic that a native multiplier must implement. It is an encoding
identity; it supplies no unit-cost group-operation instruction. -/
theorem elementCode_mul {n : Nat} (C : PrimeOrderParameters n)
    (a b : C.parameters.Element) :
    C.elementCode.encode (C.parameters.mul a b) =
      Machine.Binary.encode (n + 3) (a.val.val.val * b.val.val.val % C.modulus) := by
  change Machine.Binary.encode (n + 3) ((a.val.val * b.val.val).val) = _
  rw [ZMod.val_mul]

theorem elementCode_power {n : Nat} (C : PrimeOrderParameters n)
    (a : C.parameters.Element) (x : C.parameters.Scalar) :
    C.elementCode.encode (C.parameters.power a x) =
      Machine.Binary.encode (n + 3) (a.val.val.val ^ x.val % C.modulus) := by
  let : NeZero C.modulus := ⟨C.modulus_prime.ne_zero⟩
  have hCast : ((a.val.val.val ^ x.val : Nat) : ZMod C.modulus) =
      a.val.val ^ x.val := by
    rw [Nat.cast_pow, ZMod.natCast_zmod_val]
  change Machine.Binary.encode (n + 3) ((a.val.val ^ x.val).val) = _
  rw [← hCast, ZMod.val_natCast]

/-- Exact numeric validity criterion for a raw element code. A native
normalizer must implement all four checks, including the modular-power
membership test. This mathematical criterion does not discharge that
machine-code obligation. -/
theorem elementCode_valid_iff {n : Nat} (C : PrimeOrderParameters n) (bits : List Bool) :
    (∃ a : C.subgroup, C.elementCode.decode bits = some a) ↔
      bits.length = n + 3 ∧ Machine.Binary.value bits < C.modulus ∧
        Machine.Binary.value bits ≠ 0 ∧
        Machine.Binary.value bits ^ C.scalarOrder % C.modulus = 1 := by
  classical
  let : Fact C.modulus.Prime := ⟨C.modulus_prime⟩
  by_cases hLength : bits.length = n + 3
  · by_cases hRange : Machine.Binary.value bits < C.modulus ∧ Machine.Binary.value bits ≠ 0
    · let unit := unitOfResidue C.modulus C.modulus_prime (Machine.Binary.value bits) hRange
      have hValue : unit.val.val = Machine.Binary.value bits := by
        dsimp only [unit]
        rw [unitOfResidue_val, ZMod.val_natCast, Nat.mod_eq_of_lt hRange.1]
      have hRoot : unit ^ C.scalarOrder = 1 ↔
          Machine.Binary.value bits ^ C.scalarOrder % C.modulus = 1 := by
        rw [← C.mem_subgroup_iff, C.mem_subgroup_iff_residue, hValue]
      by_cases hPower : unit ^ C.scalarOrder = 1
      · constructor
        · intro _; exact ⟨hLength, hRange.1, hRange.2, hRoot.mp hPower⟩
        · intro _
          dsimp only [unit] at hPower
          exact ⟨⟨unit, (C.mem_subgroup_iff unit).mpr hPower⟩,
            by simp [elementCode, hLength, hRange, unit, hPower]⟩
      · have hNot : Machine.Binary.value bits ^ C.scalarOrder % C.modulus ≠ 1 :=
          fun h => hPower (hRoot.mpr h)
        dsimp only [unit] at hPower
        simp [elementCode, hLength, hRange, hPower, hNot]
    · simp [elementCode, hLength, hRange, ← and_assoc]
  · simp [elementCode, hLength]

/-- A successfully decoded fixed-width element code is already canonical.
This lets a finite choose normalizer retain the two raw element fields on
the accepting path; it need not compute a second mathematical encoding. -/
theorem elementCode_encode_decode {n : Nat} (C : PrimeOrderParameters n)
    (bits : List Bool) (a : C.subgroup)
    (h : C.elementCode.decode bits = some a) :
    C.elementCode.encode a = bits := by
  classical
  have hValid := (C.elementCode_valid_iff bits).mp ⟨a, h⟩
  obtain ⟨hWidth, hRange, hNonzero, hPower⟩ := hValid
  let : Fact C.modulus.Prime := ⟨C.modulus_prime⟩
  let unit := unitOfResidue C.modulus C.modulus_prime
    (Machine.Binary.value bits) ⟨hRange, hNonzero⟩
  have hRoot : unit ^ C.scalarOrder = 1 := by
    rw [← C.mem_subgroup_iff, C.mem_subgroup_iff_residue]
    rw [unitOfResidue_val, ZMod.val_natCast, Nat.mod_eq_of_lt hRange]
    exact hPower
  have hDecoded : a = ⟨unit, (C.mem_subgroup_iff unit).mpr hRoot⟩ := by
    have hCode : C.elementCode.decode bits =
        some (⟨unit, (C.mem_subgroup_iff unit).mpr hRoot⟩ : C.subgroup) := by
      simp [elementCode, hWidth, hRange, hNonzero, unit, hRoot]
    exact Option.some.inj (h.symm.trans hCode)
  subst a
  change Machine.Binary.encode (n + 3) unit.val.val = bits
  rw [unitOfResidue_val, ZMod.val_natCast, Nat.mod_eq_of_lt hRange, ← hWidth]
  exact Machine.Binary.encode_value bits

/-- Public parameter descriptions contain only the three fixed-width
numbers `p`, `q`, and the generator residue. Proof fields are checked by the
mathematical decoder and are not serialized. This codec does not claim that
parameter validation has a polynomial machine implementation. -/
noncomputable def instanceCode (n : Nat) :
    Machine.FiniteBitEncoding (PrimeOrderParameters n) := by
  classical
  exact
    { encode := fun C => Machine.Binary.encode (n + 3) C.modulus ++
        Machine.Binary.encode (n + 3) C.scalarOrder ++
        Machine.Binary.encode (n + 3) C.generator.val.val
      decode := fun bits =>
        if bits.length = 3 * (n + 3) then
          let p := Machine.Binary.value (bits.take (n + 3))
          let q := Machine.Binary.value ((bits.drop (n + 3)).take (n + 3))
          let v := Machine.Binary.value (bits.drop (2 * (n + 3)))
          if hp : p.Prime then
            if hq : q.Prime then
              if hSize : p < 2 ^ (n + 3) then
                if hv : v < p ∧ v ≠ 0 then
                  let g := unitOfResidue p hp v hv
                  if hg : orderOf g = q then
                    some {
                      modulus := p
                      scalarOrder := q
                      modulus_prime := hp
                      scalarOrder_prime := hq
                      generator := g
                      generator_order := hg
                      modulus_lt := hSize }
                  else none
                else none
              else none
            else none
          else none
        else none
      decode_encode := by
        intro C
        let : Fact C.modulus.Prime := ⟨C.modulus_prime⟩
        have hRange : C.generator.val.val < C.modulus := ZMod.val_lt _
        have hNonzero : C.generator.val.val ≠ 0 := by
          intro hz
          have hCast := ZMod.natCast_zmod_val C.generator.val
          rw [hz, Nat.cast_zero] at hCast
          exact Units.ne_zero C.generator hCast.symm
        have hUnit : unitOfResidue C.modulus C.modulus_prime C.generator.val.val
            ⟨hRange, hNonzero⟩ = C.generator := by
          apply Units.ext
          rw [unitOfResidue_val, ZMod.natCast_zmod_val]
        have hScalar : C.scalarOrder < 2 ^ (n + 3) :=
          C.scalarOrder_lt_modulus.trans C.modulus_lt
        simp only [List.length_append, Machine.Binary.encode_length]
        have hLength : n + 3 + (n + 3) + (n + 3) = 3 * (n + 3) := by omega
        simp only [hLength, ↓reduceIte]
        have hFirst :
            ((Machine.Binary.encode (n + 3) C.modulus ++
              Machine.Binary.encode (n + 3) C.scalarOrder) ++
              Machine.Binary.encode (n + 3) C.generator.val.val).take (n + 3) =
              Machine.Binary.encode (n + 3) C.modulus := by
          rw [List.append_assoc]
          exact List.take_left' (Machine.Binary.encode_length _ _)
        have hSecond :
            (((Machine.Binary.encode (n + 3) C.modulus ++
              Machine.Binary.encode (n + 3) C.scalarOrder) ++
              Machine.Binary.encode (n + 3) C.generator.val.val).drop (n + 3)).take (n + 3) =
              Machine.Binary.encode (n + 3) C.scalarOrder := by
          rw [List.append_assoc, List.drop_left' (Machine.Binary.encode_length _ _)]
          exact List.take_left' (Machine.Binary.encode_length _ _)
        have hThird :
            ((Machine.Binary.encode (n + 3) C.modulus ++
              Machine.Binary.encode (n + 3) C.scalarOrder) ++
              Machine.Binary.encode (n + 3) C.generator.val.val).drop (2 * (n + 3)) =
              Machine.Binary.encode (n + 3) C.generator.val.val := by
          apply List.drop_left'
          simp only [List.length_append, Machine.Binary.encode_length]
          omega
        rw [hFirst, hSecond, hThird]
        rw [Machine.Binary.value_encode C.modulus_lt,
          Machine.Binary.value_encode hScalar,
          Machine.Binary.value_encode (hRange.trans C.modulus_lt)]
        simp only [C.modulus_prime, C.scalarOrder_prime, C.modulus_lt, hRange,
          ↓reduceDIte, hUnit, C.generator_order]
        split_ifs with h
        · rfl
        · exact False.elim (h ⟨trivial, hNonzero⟩) }

@[simp] theorem instanceCode_length (n : Nat) (C : PrimeOrderParameters n) :
    ((instanceCode n).encode C).length = 3 * (n + 3) := by
  simp only [instanceCode, List.length_append, Machine.Binary.encode_length]
  omega

theorem instanceCode_decode_wrong_length (n : Nat) (bits : List Bool)
    (h : bits.length ≠ 3 * (n + 3)) : (instanceCode n).decode bits = none := by
  classical
  simp [instanceCode, h]

end PrimeOrderParameters
end ElGamal
