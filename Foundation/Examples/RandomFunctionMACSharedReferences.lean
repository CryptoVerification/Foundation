import Foundation.Crypto.Semantics.Oracle.SharedReferenceSwitch
import Foundation.Crypto.Semantics.Oracle.SharedReferenceCache
import Foundation.Examples.RandomFunctionMACStructuralTransport

/-! Wire aliases at the actual first-response cut, then resume the ORIGINAL
remaining adaptive MAC program through a single live recoded cache. This is
not postprocessing two completed runs. No native pointer implementation or CPU
bound for routing is claimed. The public physical transcript is unchanged. -/
namespace Foundation.Symmetric.RandomFunctionMACSharedReferences
open Foundation.Probability Foundation.Logic.Polygraph.StructuralTransport
open CryptoOracle CryptoOracle.RandomOracle
open RandomFunctionMACScopedEdit (repairedFamily repairedGame localDeclaration)
open RandomFunctionMACRepresentationSwitch (oldCodec old_oracle choose)
open RandomFunctionMACStructuralTransport (recordShape view viewCell)
open RandomFunctionMACNativeCaller (target)

abbrev Aliases := SharedReference.Ref × SharedReference.Ref
abbrev Past := Representation.Switch.Past (Fin 8) (Fin 256) Bool (Fin 256)
abbrev Changed := Representation.Switch.Retained (Fin 8) (Fin 256) Bool (Fin 256) Bool (Bits 8)

def codecs : Bool → Fin 8 → Fin 256 ≃ Bits 8 :=
  Representation.GeneratedEdit.codecs repairedFamily RandomFunctionMACNativeCaller.Backend.tagEquiv

def inputs (_ : Past) : recordShape.Value (fun _ => SharedReference.Ref) := .root

def aliases (past : Past) : Aliases := view.eval (fun _ => SharedReference.Ref) (inputs past)

def select (refs : Aliases) (position : Nat) : SharedReference.Ref :=
  if position % 2 = 0 then refs.1 else refs.2

def route (_ : Past) : Aliases → Nat → SharedReference.Ref := select

noncomputable def game : PMF (Aliases × Changed) :=
  Representation.SharedSwitch.wired oldCodec codecs choose view inputs route 1 target []

noncomputable def simpleGame : PMF (Aliases × Changed) :=
  Representation.SharedSwitch.wired oldCodec codecs choose (.copy recordShape) inputs route 1 target []

theorem diagram_game : game = simpleGame :=
  Representation.SharedSwitch.cell_joint viewCell oldCodec codecs choose inputs route 1 target []

theorem same_actual_game : game.map Prod.snd = repairedGame :=
  Representation.SharedSwitch.forget_view oldCodec codecs choose aliases route 1 target []

theorem same_declared_game : game.map Prod.snd =
    Representation.GeneratedEdit.rawJoint localDeclaration oldCodec RandomFunctionMACNativeCaller.Backend.tagEquiv
      choose 1 target [] := same_actual_game.trans RandomFunctionMACScopedEdit.local_repair_sound.1

theorem decoded_joint : game.map (fun pair => (pair.1, Representation.Switch.decode oldCodec codecs pair.2)) =
    RandomFunctionMACRepresentationSwitch.original.map (fun record => (aliases record.1, record)) :=
  Representation.SharedSwitch.decoded_joint oldCodec codecs choose aliases route 1 target []

theorem final_game :
    game.map (fun pair => (Representation.Switch.decode oldCodec codecs pair.2).2.2) =
      target.run RandomOracle.oracle [] := by
  have law := Representation.SharedSwitch.final_game oldCodec codecs choose aliases route 1 target []
  change game.map (fun pair => (Representation.Switch.decode oldCodec codecs pair.2).2.2) =
    target.run (Representation.oracle oldCodec) [] at law
  rw [old_oracle] at law
  exact law

theorem physical_query_bound (out : Aliases × Changed) (supported : out ∈ game.support) :
    out.2.2.2.trace.length ≤ 4 := by
  have bounded : target.BoundedQueries 4 := by
    rw [RandomFunctionMACNativeCaller.target_eq_checked]
    exact RandomFunctionMACSchedules.Examples.reduction_queries
  have decodedSupport : (Representation.Switch.decode oldCodec codecs out.2).2.2 ∈
      (target.run RandomOracle.oracle []).support := by
    rw [← final_game]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨out, supported, rfl⟩
  exact bounded.trace_length_le RandomOracle.oracle [] _ decodedSupport

/-- Either alias reads the actual recoded old cache entry. No per-alias
cache is allocated, and no new random response is drawn on this hit. -/
theorem alias_cache_hit (reference : SharedReference.Ref) (mask : Bool) (input : Fin 8) (tag : Fin 256) :
    SharedReference.service (Representation.oracle (codecs mask))
      (Representation.Switch.recode oldCodec (codecs mask) [(input, tag)]) (reference, input) =
      PMF.pure (Representation.Switch.recode oldCodec (codecs mask) [(input, tag)], tag) := by
  simp [SharedReference.service, Representation.oracle, Representation.Switch.recode, Representation.table, oldCodec]

/-- info: (true, [true, true, true]) -/
#guard_msgs in
#eval (decide ((show Aliases from view.eval (fun _ => SharedReference.Ref) .root) = (.root, .root)),
  (List.range 3).map (fun position => decide (select (.root, .root) position = .root)))

end Foundation.Symmetric.RandomFunctionMACSharedReferences
