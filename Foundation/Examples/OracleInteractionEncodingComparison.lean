import Foundation.Examples.OracleInteractionEncodingBaseline
import Foundation.Examples.OracleInteractionReplayComparison

/-! A controlled representation-change task for the same action fragment.
Both methods reuse the supplied swap script and old local probability facts.
The example changes stored values nontrivially and retains public responses. -/
namespace CryptoOracle.ProofEdits.Interaction.Encoding.Comparison
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
section General
variable {Input Tag : Type} [DecidableEq Input] [Fintype Tag] [Nonempty Tag]
    (codecs next : Input → Tag ≃ Tag)

theorem diagram_run {first second : List (Action Input)} (cell : Cell first second) (stored : State Input Tag) :
    run codecs first stored = run codecs second stored :=
  transport codecs (fun plain => cell.sound plain) stored

theorem diagram_repair {first second : List (Action Input)} (cell : Cell first second) (stored : State Input Tag) :
    (run codecs first stored).map (recode codecs next) = run next second (recode codecs next stored) := by
  rw [recode_run, diagram_run next cell]

theorem validated_diagram_repair (seen : Finset Input) (first second : List (Action Input)) (positions : List Nat)
    (accepted : Certificate.validates seen first second positions = true) (stored : State Input Tag) :
    (run codecs first stored).map (recode codecs next) = run next second (recode codecs next stored) := by
  obtain ⟨_, cell, _, _⟩ := Certificate.validates_sound seen first second positions accepted
  exact diagram_repair codecs next cell stored

/-- Same conclusion from the ordinary checker, for every script accepted
by the diagram checker. There is no path-enumeration restriction. -/
theorem ordinary_repair_from_diagram_validation (seen : Finset Input)
    (first second : List (Action Input)) (positions : List Nat)
    (accepted : Certificate.validates seen first second positions = true) (stored : State Input Tag) :
    (run codecs first stored).map (recode codecs next) = run next second (recode codecs next stored) := by
  rw [ReplayComparison.validates_eq] at accepted
  exact Baseline.repair codecs next seen first second positions accepted stored

theorem validated_diagram_repair_joint {Context : Type} (seen : Finset Input)
    (first second : List (Action Input)) (positions : List Nat)
    (accepted : Certificate.validates seen first second positions = true)
    (prefixLaw : PMF (Context × State Input Tag)) :
    (prefixLaw.bind fun original => (run codecs first original.2).map
      (fun final => (original, recode codecs next final))) =
    (prefixLaw.bind fun original => (run next second (recode codecs next original.2)).map
      (fun final => (original, final))) := by
  congr 1
  funext original
  have law := congrArg (PMF.map (fun final => (original, final)))
    (validated_diagram_repair codecs next seen first second positions accepted original.2)
  simpa only [PMF.map_comp, Function.comp_def] using law

theorem ordinary_joint_from_diagram_validation {Context : Type} (seen : Finset Input)
    (first second : List (Action Input)) (positions : List Nat)
    (accepted : Certificate.validates seen first second positions = true)
    (prefixLaw : PMF (Context × State Input Tag)) :
    (prefixLaw.bind fun original => (run codecs first original.2).map
      (fun final => (original, recode codecs next final))) =
    (prefixLaw.bind fun original => (run next second (recode codecs next original.2)).map
      (fun final => (original, final))) := by
  rw [ReplayComparison.validates_eq] at accepted
  exact Baseline.repair_joint codecs next seen first second positions accepted prefixLaw

end General

namespace ByteExample

/-- A nontrivial permutation of all 256 tags, proved by arithmetic rather
than by choosing a few sample values. -/
def complement : Fin 256 ≃ Fin 256 where
  toFun := fun tag => ⟨255 - tag.val, by omega⟩
  invFun := fun tag => ⟨255 - tag.val, by omega⟩
  left_inv := by intro tag; apply Fin.ext; simp only; omega
  right_inv := by intro tag; apply Fin.ext; simp only; omega

/-- Even input coordinates use the complement; odd coordinates stay plain. -/
def codecs (input : Fin 8) : Fin 256 ≃ Fin 256 :=
  if input.val % 2 = 0 then complement else Equiv.refl _

def plain : State (Fin 8) (Fin 256) := ⟨[], [], [], fun _ => 0⟩

theorem encoding_changes_secret : state codecs plain ≠ plain := by
  intro same
  have changed := congrArg (fun value : State (Fin 8) (Fin 256) => (value.function 0).val) same
  norm_num [state, plain, codecs, complement] at changed

theorem coordinate_difference : (state codecs plain).function 0 = 255 ∧ (state codecs plain).function 1 = 0 := by
  constructor <;> rfl

theorem public_response : (ask codecs (state codecs plain) 0).reverseTrace = [(0, 0)] := rfl

/-- Reusing the original lookup operation would publish the internal code
255 instead of response 0. The diagnostic catches that real mismatch. -/
theorem rejects_undecoded_history :
    (Interaction.ask (state codecs plain) 0).reverseTrace ≠ (ask codecs (state codecs plain) 0).reverseTrace := by decide

def beforeWord : List (Action (Fin 8)) := [.refresh 7, .record 0, .query 0]
def afterWord : List (Action (Fin 8)) := [.query 0, .record 0, .refresh 7]

theorem ordinary_accepts : ReplayBaseline.validates {0, 2} beforeWord afterWord [0, 1, 0] = true := by decide

theorem diagram_accepts : Certificate.validates {0, 2} beforeWord afterWord [0, 1, 0] = true := by decide

/-- The representation changes from plain values to coordinate-dependent
encoded values. The original three-swap script remains unchanged. -/
theorem ordinary_repair (initial : State (Fin 8) (Fin 256)) :
    (run (fun _ => Equiv.refl _) beforeWord initial).map
      (recode (fun _ => Equiv.refl _) codecs) =
    run codecs afterWord (recode (fun _ => Equiv.refl _) codecs initial) :=
  Baseline.repair (fun _ => Equiv.refl _) codecs {0, 2} beforeWord afterWord [0, 1, 0] ordinary_accepts initial

theorem diagram_repair (initial : State (Fin 8) (Fin 256)) :
    (run (fun _ => Equiv.refl _) beforeWord initial).map
      (recode (fun _ => Equiv.refl _) codecs) =
    run codecs afterWord (recode (fun _ => Equiv.refl _) codecs initial) :=
  validated_diagram_repair (fun _ => Equiv.refl _) codecs {0, 2} beforeWord afterWord [0, 1, 0] diagram_accepts initial

end ByteExample
end CryptoOracle.ProofEdits.Interaction.Encoding.Comparison
