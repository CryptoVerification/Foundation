import Foundation.Crypto.Semantics.Oracle.GeneratedRepresentationEdit
import Foundation.Examples.RandomFunctionMACRepresentationSwitch
import Mathlib.Algebra.Group.Fin.Basic

/-! An actual MAC representation edit specified by FORWARD byte arithmetic.
No inverse is supplied. The checked finite compiler constructs it, then the
generated represented oracle recodes and resumes the original continuation. -/
namespace Foundation.Symmetric.RandomFunctionMACGeneratedEdit
open Foundation.Probability Foundation.Logic
open CryptoOracle CryptoOracle.RandomOracle
open RandomFunctionMACNativeCaller (target)
open RandomFunctionMACRepresentationSwitch (oldCodec old_oracle choose)

def declaration (index : Bool × Fin 8) (tag : Fin 256) : Fin 256 := tag + (if index.1 then 1 else 0)

theorem declaration_bijective (index : Bool × Fin 8) : Function.Bijective (declaration index) := by
  exact (Equiv.addRight (if index.1 then (1 : Fin 256) else 0)).bijective

theorem compiler_accepts : (FiniteCodecGenerator.compileFamily declaration).isSome = true :=
  (FiniteCodecGenerator.family_complete declaration).mpr declaration_bijective

def generatedFamily : Bool × Fin 8 → Fin 256 ≃ Fin 256 :=
  (FiniteCodecGenerator.compileFamily declaration).get compiler_accepts

theorem compiled : FiniteCodecGenerator.compileFamily declaration = some generatedFamily := by
  exact (Option.some_get compiler_accepts).symm

def newCodec : Bool → Fin 8 → Fin 256 ≃ Bits 8 :=
  Representation.GeneratedEdit.codecs generatedFamily RandomFunctionMACNativeCaller.Backend.tagEquiv

noncomputable def switched := Representation.Switch.joint oldCodec newCodec choose 1 target []

theorem generated_game :
    Representation.GeneratedEdit.generate declaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
      choose 1 target [] = some (generatedFamily, switched) := by
  simp only [Representation.GeneratedEdit.generate, compiled, Option.map_some]
  rfl

theorem matches_declared_edit : switched =
    Representation.GeneratedEdit.rawJoint declaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
      choose 1 target [] :=
  Representation.GeneratedEdit.generated_matches_edit declaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
    choose 1 target [] generatedFamily switched generated_game

theorem declared_encoding (mask : Bool) (input : Fin 8) (tag : Fin 256) :
    newCodec mask input tag = RandomFunctionMACNativeCaller.Backend.tagEquiv (declaration (mask, input) tag) := by
  exact (Representation.GeneratedEdit.generate_sound declaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
    choose 1 target [] generatedFamily switched generated_game).1 mask input tag

theorem decoded_joint : switched.map (Representation.Switch.decode oldCodec newCodec) =
    RandomFunctionMACRepresentationSwitch.original := by
  exact (Representation.GeneratedEdit.generate_sound declaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
    choose 1 target [] generatedFamily switched generated_game).2

theorem decoded_game :
    switched.map (fun pair => (Representation.Switch.decode oldCodec newCodec pair).2.2) =
      target.run RandomOracle.oracle [] := by
  have law := Representation.GeneratedEdit.generated_final declaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
    choose 1 target [] generatedFamily switched generated_game
  change switched.map (fun pair => (Representation.Switch.decode oldCodec newCodec pair).2.2) =
    target.run (Representation.oracle oldCodec) [] at law
  rw [old_oracle] at law
  exact law

theorem selection_uniform : switched.map (fun pair => pair.2.1) = uniform Bool := by
  have newPrefix := Representation.Switch.prefix_selection oldCodec newCodec choose 1 target []
  rw [old_oracle] at newPrefix
  have same := newPrefix.trans RandomFunctionMACRepresentationSwitch.prefix_and_selection.symm
  have projected := congrArg (fun p => p.map Prod.snd) same
  simp only [PMF.map_comp, Function.comp_def] at projected
  exact projected.trans RandomFunctionMACRepresentationSwitch.selection_law

def badDeclaration (index : Bool × Fin 8) (tag : Fin 256) : Fin 256 := if index.1 then 0 else tag

theorem collision_rejected : FiniteCodecGenerator.compileFamily badDeclaration = none := by
  unfold FiniteCodecGenerator.compileFamily
  split
  · rename_i checked
    have injective := ((FiniteCodecGenerator.validates_bijective (badDeclaration (true, 0))).mp
      (checked (true, 0))).1
    have same : (0 : Fin 256) = 1 := injective (show badDeclaration (true, 0) 0 = badDeclaration (true, 0) 1 from rfl)
    exact False.elim ((by decide : (0 : Fin 256) ≠ 1) same)
  · rfl

theorem no_randomized_collision_decoder :
    ¬∃ decoder : Fin 256 → PMF (Fin 256), ∀ tag, decoder (badDeclaration (true, 0) tag) = PMF.pure tag := by
  intro decoder
  have checked := (Representation.GeneratedEdit.randomized_decoder_iff (badDeclaration (true, 0))).mp decoder
  have injective := ((FiniteCodecGenerator.validates_bijective _).mp checked).1
  have impossible : (0 : Fin 256) = 1 := injective (show badDeclaration (true, 0) 0 = badDeclaration (true, 0) 1 from rfl)
  exact (by decide : (0 : Fin 256) ≠ 1) impossible

/-- A global compiler may reject a declaration at an UNUSED input. This is
a verified limit on completeness for whole-program semantic equivalence. -/
def ignoredDeclaration (index : Bool × Fin 8) (tag : Fin 256) : Fin 256 :=
  if index.2 = 6 then 0 else declaration index tag

theorem unused_declaration_rejected : FiniteCodecGenerator.compileFamily ignoredDeclaration = none := by
  unfold FiniteCodecGenerator.compileFamily
  split
  · rename_i checked
    have injective := ((FiniteCodecGenerator.validates_bijective (ignoredDeclaration (false, 6))).mp
      (checked (false, 6))).1
    have impossible : (0 : Fin 256) = 1 := injective
      (show ignoredDeclaration (false, 6) 0 = ignoredDeclaration (false, 6) 1 from rfl)
    exact False.elim ((by decide : (0 : Fin 256) ≠ 1) impossible)
  · rfl

/-- Although the compiler rejects globally, the actual MAC cannot observe
the changed entry at message 6. This compares STATIC labels from empty state,
not the complete adaptive switch after an arbitrary saved prefix. -/
theorem unused_raw_game_equal (mask : Bool) :
    target.run (Representation.GeneratedEdit.rawOracle (fun input => ignoredDeclaration (mask, input))
      RandomFunctionMACNativeCaller.Backend.tagEquiv) [] =
    target.run (Representation.GeneratedEdit.rawOracle (fun input => declaration (mask, input))
      RandomFunctionMACNativeCaller.Backend.tagEquiv) [] := by
  apply Representation.GeneratedEdit.raw_run_congr _ _ _ {0, 1, 2, 3, 7} target
    (by rw [RandomFunctionMACQueryFootprint.target_footprint])
  intro input member
  have different : input ≠ 6 := by intro same; simp [same] at member
  funext tag
  simp only [ignoredDeclaration, if_neg different]

/-- info: (true, false) -/
#guard_msgs in
#eval ((FiniteCodecGenerator.compileFamily declaration).isSome,
  (FiniteCodecGenerator.compileFamily badDeclaration).isSome)

/-- info: (0, 255) -/
#guard_msgs in
#eval ((generatedFamily (true, 0) 255).val, ((generatedFamily (true, 0)).symm 0).val)

/-- info: false -/
#guard_msgs in
#eval (FiniteCodecGenerator.compileFamily ignoredDeclaration).isSome

end Foundation.Symmetric.RandomFunctionMACGeneratedEdit
