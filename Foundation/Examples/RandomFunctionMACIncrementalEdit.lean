import Foundation.Crypto.Semantics.Oracle.IncrementalRepresentationEdit
import Foundation.Examples.RandomFunctionMACScopedEdit

/-! Incremental revalidation of the actual MAC representation edit. The old
certificate and unchanged-row proof are explicit and reusable. This file does
not benchmark proof construction, execution of the game, or native recoding. -/
namespace Foundation.Symmetric.RandomFunctionMACIncrementalEdit
open Foundation.Probability Foundation.Logic
open CryptoOracle CryptoOracle.RandomOracle
open RandomFunctionMACScopedEdit
open RandomFunctionMACGeneratedEdit (ignoredDeclaration)
open RandomFunctionMACNativeCaller (target)
open RandomFunctionMACRepresentationSwitch (oldCodec choose)

theorem unchanged : ∀ index ∈ finiteScope, index ∉ changed → ignoredDeclaration index = localDeclaration index := by
  intro index _ untouched
  have different : index.2 ≠ 7 := by
    intro same
    exact untouched (Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr same⟩)
  funext tag
  simp only [localDeclaration, if_neg different]

def compiled := FiniteCodecRepair.compile finiteScope changed ignoredDeclaration localDeclaration scoped_accepts unchanged

theorem compiled_eq_full : compiled = FiniteCodecRestriction.compile finiteScope localDeclaration :=
  FiniteCodecRepair.compile_eq_full finiteScope changed ignoredDeclaration localDeclaration scoped_accepts unchanged

theorem compiled_eq_previous : compiled = some repairedFamily := by
  rw [compiled_eq_full]
  exact (Option.some_get local_repair_accepts).symm

theorem accepted_scope :
    (FiniteCodecRestriction.compile (Representation.ScopedEdit.used target ([] : Table (Fin 8) (Fin 256)))
      ignoredDeclaration).isSome = true := by
  rw [exact_scope]
  exact scoped_accepts

theorem unchanged_scope : ∀ index ∈ Representation.ScopedEdit.used target ([] : Table (Fin 8) (Fin 256)),
    index ∉ changed → ignoredDeclaration index = localDeclaration index := by
  simpa only [exact_scope] using unchanged

theorem generated :
    Representation.IncrementalEdit.generate changed ignoredDeclaration localDeclaration oldCodec
      RandomFunctionMACNativeCaller.Backend.tagEquiv choose 1 target [] accepted_scope unchanged_scope =
      some (repairedFamily, repairedGame) := by
  rw [Representation.IncrementalEdit.generate_eq_full]
  exact local_repair_generated

theorem joint_sound :
    repairedGame = Representation.GeneratedEdit.rawJoint localDeclaration oldCodec
      RandomFunctionMACNativeCaller.Backend.tagEquiv choose 1 target [] ∧
    repairedGame.map (Representation.Switch.decode oldCodec
      (Representation.GeneratedEdit.codecs repairedFamily RandomFunctionMACNativeCaller.Backend.tagEquiv)) =
      RandomFunctionMACRepresentationSwitch.original :=
  Representation.IncrementalEdit.generate_sound changed ignoredDeclaration localDeclaration oldCodec
    RandomFunctionMACNativeCaller.Backend.tagEquiv choose 1 target [] accepted_scope unchanged_scope
    repairedFamily repairedGame generated

def badLocal (index : Bool × Fin 8) (tag : Fin 256) : Fin 256 :=
  if index.2 = 7 then 0 else ignoredDeclaration index tag

theorem bad_unchanged : ∀ index ∈ finiteScope, index ∉ changed → ignoredDeclaration index = badLocal index := by
  intro index _ untouched
  have different : index.2 ≠ 7 := by
    intro same
    exact untouched (Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr same⟩)
  funext tag
  simp only [badLocal, if_neg different]

def rejected := FiniteCodecRepair.compile finiteScope changed ignoredDeclaration badLocal scoped_accepts bad_unchanged

theorem rejects_collision : rejected.isSome = false := by
  have failure : rejected.isSome ≠ true := by
    intro success
    have checked := (FiniteCodecRepair.complete finiteScope changed ignoredDeclaration badLocal scoped_accepts bad_unchanged).mp success
    have included : (true, (7 : Fin 8)) ∈ finiteScope ∩ changed := by decide_cbv
    have injective := (checked (true, 7) included).1
    have impossible : (0 : Fin 256) = 1 := injective (show badLocal (true, 7) 0 = badLocal (true, 7) 1 from rfl)
    exact (by decide : (0 : Fin 256) ≠ 1) impossible
  exact Bool.eq_false_iff.mpr failure

/-- info: (true, false, 2, 10) -/
#guard_msgs in
#eval (compiled.isSome, rejected.isSome, (finiteScope ∩ changed).card, finiteScope.card)

end Foundation.Symmetric.RandomFunctionMACIncrementalEdit
