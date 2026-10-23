import Foundation.Crypto.Semantics.Oracle.AutomaticRepresentationEdit
import Foundation.Crypto.Logic.Polygraph.RepresentationPatches
import Foundation.Examples.RandomFunctionMACIncrementalEdit

/-! Exact changes and a concrete replacement path are computed from the two
MAC declarations. An elementary exchange diagram compares the two update
orders, and both orders generate the same actual dynamically switched game. -/
namespace Foundation.Symmetric.RandomFunctionMACAutomaticEdit
open Foundation.Probability Foundation.Logic
open CryptoOracle CryptoOracle.RandomOracle
open RandomFunctionMACScopedEdit
open RandomFunctionMACGeneratedEdit (ignoredDeclaration)
open RandomFunctionMACNativeCaller (target)
open RandomFunctionMACRepresentationSwitch (oldCodec choose)
open Representation

def computed := FiniteCodecDifference.changed finiteScope ignoredDeclaration localDeclaration

theorem row_changed (index : Bool × Fin 8) :
    ignoredDeclaration index ≠ localDeclaration index ↔ index.2 = 7 := by
  by_cases atSeven : index.2 = 7
  · constructor
    · intro _
      exact atSeven
    · intro _ equal
      have notSix : index.2 ≠ 6 := by rw [atSeven]; decide
      have zero := congrFun equal 0
      simp only [ignoredDeclaration, if_neg notSix, localDeclaration, if_pos atSeven,
        RandomFunctionMACGeneratedEdit.declaration] at zero
      cases label : index.1
      · rw [label] at zero
        have impossible : (0 : Fin 256) = 2 := zero
        exact (by decide : (0 : Fin 256) ≠ 2) impossible
      · rw [label] at zero
        have impossible : (1 : Fin 256) = 3 := zero
        exact (by decide : (1 : Fin 256) ≠ 3) impossible
  · have same : ignoredDeclaration index = localDeclaration index := by
      funext tag
      simp only [localDeclaration, if_neg atSeven]
    exact iff_of_false (fun different => different same) atSeven

theorem exact_changes : computed = changed := by
  ext index
  rw [computed, FiniteCodecDifference.mem_changed, row_changed]
  constructor
  · intro member
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr member.2⟩
  · intro member
    have atSeven : index.2 = 7 := Finset.mem_singleton.mp (Finset.mem_product.mp member).2
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, by simp [inputScope, atSeven]⟩, atSeven⟩

theorem changed_count : computed.card = 2 := by rw [exact_changes]; decide_cbv

def compiled := FiniteCodecDifference.compile finiteScope ignoredDeclaration localDeclaration scoped_accepts

theorem compiled_eq_previous : compiled = some repairedFamily := by
  rw [compiled, FiniteCodecDifference.compile_eq_full]
  exact (Option.some_get local_repair_accepts).symm

theorem generated_game :
    Representation.AutomaticEdit.generate ignoredDeclaration localDeclaration oldCodec
      RandomFunctionMACNativeCaller.Backend.tagEquiv choose 1 target [] RandomFunctionMACIncrementalEdit.accepted_scope =
      some (repairedFamily, repairedGame) := by
  rw [Representation.AutomaticEdit.generate_eq_full]
  exact local_repair_generated

theorem joint_sound :
    repairedGame = Representation.GeneratedEdit.rawJoint localDeclaration oldCodec
      RandomFunctionMACNativeCaller.Backend.tagEquiv choose 1 target [] ∧
    repairedGame.map (Representation.Switch.decode oldCodec
      (Representation.GeneratedEdit.codecs repairedFamily RandomFunctionMACNativeCaller.Backend.tagEquiv)) =
      RandomFunctionMACRepresentationSwitch.original :=
  Representation.AutomaticEdit.generate_sound ignoredDeclaration localDeclaration oldCodec
    RandomFunctionMACNativeCaller.Backend.tagEquiv choose 1 target [] RandomFunctionMACIncrementalEdit.accepted_scope
    repairedFamily repairedGame generated_game

/-- Ordered enumeration of the already certified exact scope; no order on
arbitrary finite-set quotients is assumed by the path generator. -/
def rows : List (Bool × Fin 8) :=
  [(false, 0), (false, 1), (false, 2), (false, 3), (false, 7),
   (true, 0), (true, 1), (true, 2), (true, 3), (true, 7)]

theorem rows_cover : rows.toFinset = finiteScope := by decide_cbv

theorem rows_nodup : rows.Nodup := by decide_cbv

def path := Patches.generated rows ignoredDeclaration localDeclaration

theorem path_eq : path = Patches.generate [(false, 7), (true, 7)] localDeclaration := by
  simp [path, Patches.generated, rows, row_changed, Patches.generate]

theorem path_length : path.length = 2 := by rw [path_eq]; rfl

def reversedPath := Patches.generate [(true, 7), (false, 7)] localDeclaration

def exchangeDiagram : Patches.Cell path reversedPath := by
  rw [path_eq]
  exact Patches.exchangeCell (false, 7) (true, 7) [] localDeclaration

theorem path_compiled :
    FiniteCodecRestriction.compile finiteScope (Patches.run path ignoredDeclaration) = some repairedFamily := by
  rw [← rows_cover, path, Patches.generated_compile_eq, rows_cover]
  exact (Option.some_get local_repair_accepts).symm

theorem path_game :
    Representation.ScopedEdit.generate (Patches.run path ignoredDeclaration) oldCodec
      RandomFunctionMACNativeCaller.Backend.tagEquiv choose 1 target [] = some (repairedFamily, repairedGame) := by
  simp only [Representation.ScopedEdit.generate, exact_scope, path_compiled, Option.map_some]
  rfl

theorem reversed_path_game :
    Representation.ScopedEdit.generate (Patches.run reversedPath ignoredDeclaration) oldCodec
      RandomFunctionMACNativeCaller.Backend.tagEquiv choose 1 target [] = some (repairedFamily, repairedGame) := by
  rw [← exchangeDiagram.sound ignoredDeclaration]
  exact path_game

/-- info: (2, true, 2, false, 0, true) -/
#guard_msgs in
#eval (computed.card, compiled.isSome, path.length,
  (FiniteCodecDifference.compile finiteScope ignoredDeclaration RandomFunctionMACIncrementalEdit.badLocal scoped_accepts).isSome,
  (FiniteCodecDifference.changed finiteScope ignoredDeclaration ignoredDeclaration).card,
  (FiniteCodecDifference.compile finiteScope ignoredDeclaration ignoredDeclaration scoped_accepts).isSome)

end Foundation.Symmetric.RandomFunctionMACAutomaticEdit
