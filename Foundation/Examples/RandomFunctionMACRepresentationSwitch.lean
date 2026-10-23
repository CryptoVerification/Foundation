import Foundation.Crypto.Semantics.Oracle.RepresentationSwitch
import Foundation.Examples.RandomFunctionMACQueryFootprint
import Foundation.Examples.RandomFunctionMACCausalRepair

/-! Change the actual stored type AFTER the first actual MAC response.
The public first response selects an eight-bit encoding. The recoded cache
is used by the original remaining adaptive query, repeat, and verification.
The selection, prefix, and entire final outcome stay in a single joint law. -/
namespace Foundation.Symmetric.RandomFunctionMACRepresentationSwitch
open Foundation.Probability Foundation.Probability.SelectedCouplingGraph
open CryptoOracle CryptoOracle.RandomOracle
open RandomFunctionMACNativeCaller (target)
open RandomFunctionMACCausalRepair (challenge challenge_uniform)

def oldCodec (_ : Fin 8) : Fin 256 ≃ Fin 256 := Equiv.refl _

def newCodec (mask : Bool) (_ : Fin 8) : Fin 256 ≃ Bits 8 :=
  RandomFunctionMACNativeCaller.Backend.tagEquiv.trans (twistEquiv 8 mask)

abbrev Past := Representation.Switch.Past (Fin 8) (Fin 256) Bool (Fin 256)

/-- Only the actually recorded first public response is read. -/
def choose (past : Past) : Bool := challenge (((past.trace.head?).map Prod.snd).getD 0)

noncomputable def switched := Representation.Switch.joint oldCodec newCodec choose 1 target []
noncomputable def original := Representation.Switch.reference oldCodec choose 1 target []

theorem old_oracle : Representation.oracle oldCodec = (RandomOracle.oracle : Oracle (Fin 8) (Fin 256) (Table (Fin 8) (Fin 256))) := by
  funext saved input
  simp only [Representation.oracle, RandomOracle.oracle, oldCodec]
  cases found : saved.lookup input <;> rfl

theorem decoded_joint : switched.map (Representation.Switch.decode oldCodec newCodec) = original :=
  Representation.Switch.decoded_joint oldCodec newCodec choose 1 target []

theorem decoded_game :
    switched.map (fun pair => (Representation.Switch.decode oldCodec newCodec pair).2.2) =
      target.run RandomOracle.oracle [] := by
  have law := Representation.Switch.decoded_final oldCodec newCodec choose 1 target []
  simpa only [switched, old_oracle] using law

theorem original_game : original.map (fun pair => pair.2.2) = target.run RandomOracle.oracle [] := by
  have law := Representation.Switch.reference_final oldCodec choose 1 target []
  simpa only [original, old_oracle] using law

theorem prefix_and_selection : switched.map (fun pair => (pair.1, pair.2.1)) =
    ((Program.pauseAfter 1 target).run RandomOracle.oracle []).map (fun past => (past, choose past)) := by
  have law := Representation.Switch.prefix_selection oldCodec newCodec choose 1 target []
  simpa only [switched, old_oracle] using law

theorem selection_law : switched.map (fun pair => pair.2.1) = uniform Bool := by
  have selected := congrArg (fun p => p.map Prod.snd) prefix_and_selection
  simp only [PMF.map_comp, Function.comp_def] at selected
  rw [selected]
  simp only [Program.pauseAfter, target, Program.run, RandomOracle.oracle, List.lookup_nil,
    PMF.map_bind, PMF.bind_map, PMF.pure_map, Function.comp_def, choose, List.head?_cons, Option.map_some, Option.getD_some]
  change sampleBit.bind (fun _ => (uniform (Fin 256)).map challenge) = _
  rw [challenge_uniform, PMF.bind_const]

theorem decoded_continuation {Next : Type}
    (next : Representation.Switch.Retained (Fin 8) (Fin 256) Bool (Fin 256) Bool (Fin 256) → PMF Next) :
    switched.bind (fun pair => next (Representation.Switch.decode oldCodec newCodec pair)) = original.bind next :=
  Representation.Switch.decoded_continuation oldCodec newCodec choose 1 target [] next

/-- The old cache entry is actually converted before the repeated request. -/
theorem recoded_cache_hit (mask : Bool) (input : Fin 8) (tag : Fin 256) :
    Representation.oracle (newCodec mask)
      (Representation.Switch.recode oldCodec (newCodec mask) [(input, tag)]) input =
      PMF.pure (Representation.Switch.recode oldCodec (newCodec mask) [(input, tag)], tag) := by
  simp [Representation.oracle, Representation.Switch.recode, Representation.table, oldCodec]

/-- Encoding the old entry without the selected mask is not a valid switch:
the repeated public response becomes 255 instead of 0. -/
theorem stale_cache_hit :
    (Representation.oracle (newCodec true) (Representation.table (newCodec false) [(0, 0)]) 0).map Prod.snd =
      PMF.pure (255 : Fin 256) := by
  simp only [Representation.oracle, Representation.lookup, List.lookup_cons, beq_self_eq_true,
    Option.map_some, PMF.pure_map]
  congr 1

end Foundation.Symmetric.RandomFunctionMACRepresentationSwitch
