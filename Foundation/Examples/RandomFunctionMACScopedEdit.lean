import Foundation.Crypto.Semantics.Oracle.ScopedRepresentationEdit
import Foundation.Examples.RandomFunctionMACGeneratedEdit

/-! The previously rejected collision at unused message 6 is now accepted.
The scope includes initial cache keys, so preloading message 6 correctly
invalidates that declaration. Runtime checks use a precomputed EXACT scope
whose equality with the syntactic footprint is proved, not unchecked input. -/
namespace Foundation.Symmetric.RandomFunctionMACScopedEdit
open Foundation.Probability Foundation.Logic
open CryptoOracle CryptoOracle.RandomOracle
open RandomFunctionMACNativeCaller (target)
open RandomFunctionMACRepresentationSwitch (oldCodec old_oracle choose)
open RandomFunctionMACGeneratedEdit (declaration declaration_bijective ignoredDeclaration badDeclaration)

def inputScope : Finset (Fin 8) := {0, 1, 2, 3, 7}
def finiteScope : Finset (Bool × Fin 8) := Finset.univ.product inputScope
def preloadedScope : Finset (Bool × Fin 8) := Finset.univ.product (inputScope ∪ {6})

theorem exact_scope : Representation.ScopedEdit.used target ([] : Table (Fin 8) (Fin 256)) = finiteScope := by
  simp [Representation.ScopedEdit.used, Representation.Scope.allowed,
    RandomFunctionMACQueryFootprint.target_footprint, finiteScope, inputScope]

theorem exact_preloaded_scope :
    Representation.ScopedEdit.used target ([(6, 1)] : Table (Fin 8) (Fin 256)) = preloadedScope := by
  simp [Representation.ScopedEdit.used, Representation.Scope.allowed,
    RandomFunctionMACQueryFootprint.target_footprint, preloadedScope, inputScope]

theorem ten_declarations : finiteScope.card = 10 := by decide_cbv

theorem declaration_counts : finiteScope.card = 10 ∧ Fintype.card (Bool × Fin 8) = 16 := by
  exact ⟨ten_declarations, by decide⟩

theorem scoped_accepts : (FiniteCodecRestriction.compile finiteScope ignoredDeclaration).isSome = true := by
  apply (FiniteCodecRestriction.complete finiteScope ignoredDeclaration).mpr
  intro index member
  have included : index.2 ∈ inputScope := (Finset.mem_product.mp member).2
  have different : index.2 ≠ 6 := by intro same; simp [inputScope, same] at included
  have encoders : ignoredDeclaration index = declaration index := by
    funext tag
    simp only [ignoredDeclaration, if_neg different]
  rw [encoders]
  exact declaration_bijective index

def generatedFamily : Bool × Fin 8 → Fin 256 ≃ Fin 256 :=
  (FiniteCodecRestriction.compile finiteScope ignoredDeclaration).get scoped_accepts

theorem compiled :
    FiniteCodecRestriction.compile (Representation.ScopedEdit.used target ([] : Table (Fin 8) (Fin 256)))
      ignoredDeclaration = some generatedFamily := by
  rw [exact_scope]
  exact (Option.some_get scoped_accepts).symm

def newCodec : Bool → Fin 8 → Fin 256 ≃ Bits 8 :=
  Representation.GeneratedEdit.codecs generatedFamily RandomFunctionMACNativeCaller.Backend.tagEquiv

noncomputable def switched := Representation.Switch.joint oldCodec newCodec choose 1 target []

theorem generated_game :
    Representation.ScopedEdit.generate ignoredDeclaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
      choose 1 target [] = some (generatedFamily, switched) := by
  simp only [Representation.ScopedEdit.generate, compiled, Option.map_some]
  rfl

/-- Equality with the original DECLARATION, even though its unused entry
is non-injective and the proof artifact completes that entry by identity. -/
theorem matches_declared_edit : switched =
    Representation.GeneratedEdit.rawJoint ignoredDeclaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
      choose 1 target [] :=
  (Representation.ScopedEdit.generate_sound ignoredDeclaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
    choose 1 target [] generatedFamily switched generated_game).1

theorem decoded_joint : switched.map (Representation.Switch.decode oldCodec newCodec) =
    RandomFunctionMACRepresentationSwitch.original :=
  (Representation.ScopedEdit.generate_sound ignoredDeclaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
    choose 1 target [] generatedFamily switched generated_game).2

theorem decoded_game :
    switched.map (fun pair => (Representation.Switch.decode oldCodec newCodec pair).2.2) =
      target.run RandomOracle.oracle [] := by
  have law := Representation.ScopedEdit.generated_final ignoredDeclaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
    choose 1 target [] generatedFamily switched generated_game
  change switched.map (fun pair => (Representation.Switch.decode oldCodec newCodec pair).2.2) =
    target.run (Representation.oracle oldCodec) [] at law
  rw [old_oracle] at law
  exact law

theorem outside_completed : generatedFamily (false, 6) = Equiv.refl _ := by
  apply FiniteCodecRestriction.outside_spec finiteScope ignoredDeclaration generatedFamily
    (by simpa only [exact_scope] using compiled)
  decide_cbv

theorem preloaded_rejected :
    FiniteCodecRestriction.compile (Representation.ScopedEdit.used target ([(6, 1)] : Table (Fin 8) (Fin 256)))
      ignoredDeclaration = none := by
  rw [exact_preloaded_scope]
  unfold FiniteCodecRestriction.compile
  split
  · rename_i checked
    have member : (false, (6 : Fin 8)) ∈ preloadedScope := by simp [preloadedScope]
    have injective := ((FiniteCodecGenerator.validates_bijective (ignoredDeclaration (false, 6))).mp
      (checked (false, 6) member)).1
    have impossible : (0 : Fin 256) = 1 := injective (show ignoredDeclaration (false, 6) 0 = ignoredDeclaration (false, 6) 1 from rfl)
    exact False.elim ((by decide : (0 : Fin 256) ≠ 1) impossible)
  · rfl

theorem actual_collision_rejected : FiniteCodecRestriction.compile finiteScope badDeclaration = none := by
  unfold FiniteCodecRestriction.compile
  split
  · rename_i checked
    have member : (true, (0 : Fin 8)) ∈ finiteScope := by decide_cbv
    have injective := ((FiniteCodecGenerator.validates_bijective (badDeclaration (true, 0))).mp
      (checked (true, 0) member)).1
    have impossible : (0 : Fin 256) = 1 := injective (show badDeclaration (true, 0) 0 = badDeclaration (true, 0) 1 from rfl)
    exact False.elim ((by decide : (0 : Fin 256) ≠ 1) impossible)
  · rfl

/-- All labels are still checked, even if a particular selection policy
never returns true. This witnesses the remaining conservative boundary. -/
theorem unselected_label_equal :
    Representation.GeneratedEdit.rawJoint badDeclaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
      (fun _ => false) 1 target [] =
    Representation.GeneratedEdit.rawJoint declaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
      (fun _ => false) 1 target [] := by
  have same : (fun input : Fin 8 => badDeclaration (false, input)) = fun input => declaration (false, input) := by
    funext input tag
    simp [badDeclaration, declaration]
  simp only [Representation.GeneratedEdit.rawJoint, same]

/-- The valid declaration and the declaration with an unused collision
produce exactly the same generated family and dynamically switched game. -/
theorem unused_edit_reuses_artifact :
    Representation.ScopedEdit.generate declaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
      choose 1 target [] = some (generatedFamily, switched) := by
  have same : FiniteCodecRestriction.compile finiteScope declaration =
      FiniteCodecRestriction.compile finiteScope ignoredDeclaration := by
    apply FiniteCodecRestriction.compile_congr
    intro index included
    have member : index.2 ∈ inputScope := (Finset.mem_product.mp included).2
    have different : index.2 ≠ 6 := by intro same; simp [inputScope, same] at member
    funext tag
    simp only [ignoredDeclaration, if_neg different]
  simpa only [Representation.ScopedEdit.generate, exact_scope, same] using generated_game

def changed : Finset (Bool × Fin 8) := Finset.univ.product {7}

def localDeclaration (index : Bool × Fin 8) (tag : Fin 256) : Fin 256 :=
  if index.2 = 7 then tag + (if index.1 then 3 else 2) else ignoredDeclaration index tag

theorem two_changed_rows : (finiteScope ∩ changed).card = 2 := by decide_cbv

theorem local_repair_accepts : (FiniteCodecRestriction.compile finiteScope localDeclaration).isSome = true := by
  apply (FiniteCodecRestriction.repair_complete finiteScope changed ignoredDeclaration localDeclaration
    scoped_accepts (by
      intro index included untouched
      have different : index.2 ≠ 7 := by
        intro same
        exact untouched (Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr same⟩)
      funext tag
      simp only [localDeclaration, if_neg different])).mpr
  intro index included
  have hit : index.2 = 7 := by
    exact Finset.mem_singleton.mp (Finset.mem_product.mp (Finset.mem_inter.mp included).2).2
  have same : localDeclaration index = fun tag => tag + (if index.1 then 3 else 2) := by
    funext tag
    simp only [localDeclaration, if_pos hit]
  rw [same]
  exact (Equiv.addRight (if index.1 then (3 : Fin 256) else 2)).bijective

def repairedFamily : Bool × Fin 8 → Fin 256 ≃ Fin 256 :=
  (FiniteCodecRestriction.compile finiteScope localDeclaration).get local_repair_accepts

noncomputable def repairedGame := Representation.Switch.joint oldCodec
  (Representation.GeneratedEdit.codecs repairedFamily RandomFunctionMACNativeCaller.Backend.tagEquiv) choose 1 target []

theorem local_repair_generated :
    Representation.ScopedEdit.generate localDeclaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
      choose 1 target [] = some (repairedFamily, repairedGame) := by
  have accepted : FiniteCodecRestriction.compile finiteScope localDeclaration = some repairedFamily :=
    (Option.some_get local_repair_accepts).symm
  simp only [Representation.ScopedEdit.generate, exact_scope, accepted, Option.map_some]
  rfl

theorem local_repair_sound :
    repairedGame = Representation.GeneratedEdit.rawJoint localDeclaration oldCodec
      RandomFunctionMACNativeCaller.Backend.tagEquiv choose 1 target [] ∧
    repairedGame.map (Representation.Switch.decode oldCodec
      (Representation.GeneratedEdit.codecs repairedFamily RandomFunctionMACNativeCaller.Backend.tagEquiv)) =
      RandomFunctionMACRepresentationSwitch.original :=
  Representation.ScopedEdit.generate_sound localDeclaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
    choose 1 target [] repairedFamily repairedGame local_repair_generated

/-- info: (true, false, false, true) -/
#guard_msgs in
#eval ((FiniteCodecRestriction.compile finiteScope ignoredDeclaration).isSome,
  (FiniteCodecRestriction.compile preloadedScope ignoredDeclaration).isSome,
  (FiniteCodecRestriction.compile finiteScope badDeclaration).isSome,
  (FiniteCodecRestriction.compile finiteScope localDeclaration).isSome)

end Foundation.Symmetric.RandomFunctionMACScopedEdit
