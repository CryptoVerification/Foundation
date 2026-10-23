import Foundation.Crypto.Semantics.Oracle.QueryPrefix
import Foundation.Examples.RandomFunctionMACRepresentationGame

/-! Extracted effects of the existing MAC attack and complete verification
program. An encoding patch at message 7 leaves the actual signing prefix
unchanged; only the fourth query position can be affected. -/
namespace Foundation.Symmetric.RandomFunctionMACQueryFootprint
open Foundation.Probability
open CryptoOracle CryptoOracle.Program CryptoOracle.RandomOracle
open RandomFunctionMACNativeCaller (firstMessage secondMessage target)
open RandomFunctionMACRepresentationGame (codec)
open RandomFunctionMACSchedules.Examples (attack attack_queries)
set_option backward.isDefEq.respectTransparency true

@[simp] private theorem response_union_const (values : Finset (Fin 8)) :
    (Finset.univ.biUnion fun _ : Fin 256 => values) = values := by
  ext input
  simp

private theorem second_range :
    (Finset.univ.biUnion fun tag : Fin 256 => ({secondMessage tag} : Finset (Fin 8))) = {2, 3} := by
  ext input
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_singleton,
    Finset.mem_insert]
  constructor
  · rintro ⟨tag, rfl⟩
    unfold secondMessage
    split <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩

theorem first_position : footprintAt 0 target = ({0, 1} : Finset (Fin 8)) := by
  simp [target, footprintAt, firstMessage, Finset.pair_comm]

theorem second_position : footprintAt 1 target = ({2, 3} : Finset (Fin 8)) := by
  simp [target, footprintAt, second_range]

theorem repeated_position : footprintAt 2 target = ({0, 1} : Finset (Fin 8)) := by
  simp [target, footprintAt, firstMessage, Finset.pair_comm]

theorem verification_position : footprintAt 3 target = ({7} : Finset (Fin 8)) := by
  simp [target, footprintAt]

theorem no_fifth_position : footprintAt 4 target = (∅ : Finset (Fin 8)) := by
  simp [target, footprintAt]

theorem signing_positions (position : Nat) :
    footprintAt position attack =
      if position = 0 then ({0, 1} : Finset (Fin 8)) else
      if position = 1 then {2, 3} else
      if position = 2 then {0, 1} else ∅ := by
  cases position with
  | zero => simp [attack, footprintAt, Finset.pair_comm]
  | succ position =>
      cases position with
      | zero => simpa [attack, footprintAt, secondMessage] using second_range
      | succ position =>
          cases position with
          | zero => simp [attack, footprintAt, Finset.pair_comm]
          | succ position => simp [attack, footprintAt]

theorem signing_footprint : footprint attack = ({0, 1, 2, 3} : Finset (Fin 8)) := by
  ext input
  rw [attack_queries.footprint_positions]
  simp only [signing_positions]
  constructor
  · rintro ⟨position, small, member⟩
    interval_cases position <;> simp_all <;> tauto
  · intro member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨0, by omega, by simp⟩
    · exact ⟨0, by omega, by simp⟩
    · exact ⟨1, by omega, by simp⟩
    · exact ⟨1, by omega, by simp⟩

theorem target_bounded : target.BoundedQueries 4 :=
  .coin _ _ (fun _ => .query _ _ 3 (fun _ => .query _ _ 2 (fun _ =>
    .query _ _ 1 (fun _ => .query _ _ 0 (fun _ => .done _ 0)))))

theorem target_footprint : footprint target = ({0, 1, 2, 3, 7} : Finset (Fin 8)) := by
  ext input
  rw [target_bounded.footprint_positions]
  constructor
  · rintro ⟨position, small, member⟩
    interval_cases position <;>
      simp_all [first_position, second_position, repeated_position, verification_position] <;> tauto
  · intro member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by omega, by simp [first_position]⟩
    · exact ⟨0, by omega, by simp [first_position]⟩
    · exact ⟨1, by omega, by simp [second_position]⟩
    · exact ⟨1, by omega, by simp [second_position]⟩
    · exact ⟨3, by omega, by simp [verification_position]⟩

theorem verification_only : affectedPositions ({7} : Finset (Fin 8)) 4 target = [3] := by
  simp [affectedPositions, List.range_succ, first_position, second_position, repeated_position, verification_position]

theorem unused_patch : affectedPositions ({6} : Finset (Fin 8)) 4 target = [] := by
  simp [affectedPositions, List.range_succ, first_position, second_position, repeated_position, verification_position]

theorem codec_agrees (input : Fin 8) (different : input ≠ 7) : codec false input = codec true input := by
  simp only [codec, if_neg different]

/-- Same entire raw stored signing outcome, including adaptive requests,
repeated queries, chosen forgery, and encoded cache. No decoding is applied. -/
theorem signing_patch_unaffected (saved : Table (Fin 8) (Bits 8)) :
    attack.run (Representation.oracle (codec false)) saved =
      attack.run (Representation.oracle (codec true)) saved := by
  apply Representation.run_unaffected_patch (codec false) (codec true) {7}
  · intro input member
    exact codec_agrees input (by simpa using member)
  · rw [signing_footprint]
    decide

theorem represented_signing_law (mask : Bool) :
    attack.run (Representation.oracle (codec mask)) [] =
      RandomFunctionMACPosterior.signingHistory.map (mapState (Representation.table (codec mask))) := by
  symm
  exact Representation.run (codec mask) attack []

/-- Keeping the original plain history as well as its stored representation
gives equality of the chosen coupling, not just two separate marginals. -/
theorem retained_signing_patch :
    RandomFunctionMACPosterior.signingHistory.map
      (fun out => (out, mapState (Representation.table (codec false)) out)) =
    RandomFunctionMACPosterior.signingHistory.map
      (fun out => (out, mapState (Representation.table (codec true)) out)) := by
  simp only [PMF.map]
  apply bind_congr_of_support
  intro out supported
  have keys : ∀ input response, (input, response) ∈ out.state → input ≠ 7 := by
    intro input response member same
    have within : footprint attack ⊆ ({0, 1, 2, 3} : Finset (Fin 8)) := by
      rw [signing_footprint]
    have effect := Representation.plain_entries_in_set attack {0, 1, 2, 3} within out supported
      (input, response) member
    simp [same] at effect
  have tables := Representation.table_eq_of_agree (codec false) (codec true) out.state
    (fun input response member => codec_agrees input (keys input response member))
  simp only [Function.comp_def, mapState, tables]

/-- A genuinely changed representation at unused message 6. -/
def unusedCodec : Fin 8 → Fin 256 ≃ Bits 8 := Function.update (codec false) 6 (codec true 7)

theorem unused_codec_changed : unusedCodec 6 0 ≠ codec false 6 0 := by decide_cbv

theorem unused_encoding_patch (saved : Table (Fin 8) (Bits 8)) :
    target.run (Representation.oracle (codec false)) saved =
      target.run (Representation.oracle unusedCodec) saved := by
  apply Representation.run_unaffected_positions (codec false) unusedCodec {6} _ target 4 target_bounded unused_patch
  · intro input member
    have different : input ≠ 6 := by simpa using member
    simp only [unusedCodec, Function.update_of_ne different]

noncomputable def fullGame (mask : Bool) := target.run (Representation.oracle (codec mask)) []

theorem full_game_law (mask : Bool) :
    fullGame mask = (RandomFunctionMACRepresentationGame.storedGame (fun _ => mask)).map Prod.snd := by
  unfold fullGame
  have encoded := Representation.run (codec mask) target []
  simp only [Representation.table, List.map_nil] at encoded
  rw [← encoded]
  change ((target.run RandomOracle.oracle []).map (RandomFunctionMACRepresentationGame.encode mask)) = _
  rw [← RandomFunctionMACRepairGame.reference_game_law, PMF.map_bind]
  simp only [RandomFunctionMACRepresentationGame.storedGame, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply bind_congr_of_support
  intro past supported
  rw [RandomFunctionMACRepresentationGame.suffix_law mask past supported, PMF.map_comp]
  rfl

theorem full_storage_relation (mask : Bool) (out : RandomFunctionMACRepresentationGame.StoredOutcome)
    (supported : out ∈ (fullGame mask).support) :
    RandomFunctionMACRepresentationGame.storedAnswer out =
      Foundation.Probability.SelectedCouplingGraph.twist mask
        (RandomFunctionMACNativeCaller.Backend.tagBits
          (RandomFunctionMACRepresentationGame.publicAnswer out)) := by
  rw [full_game_law, PMF.mem_support_map_iff] at supported
  obtain ⟨pair, member, rfl⟩ := supported
  exact RandomFunctionMACRepresentationGame.stored_game_relation (fun _ => mask) pair member

/-- The affected last query actually changes the raw outcome law. Both
decoded programs still implement exactly the same original complete game. -/
theorem full_games_distinct : fullGame false ≠ fullGame true := by
  intro same
  obtain ⟨out, supported⟩ := (fullGame false).support_nonempty
  have plain := full_storage_relation false out supported
  rw [same] at supported
  have masked := full_storage_relation true out supported
  rw [RandomFunctionMACRepresentationGame.untwisted] at plain
  have fixed := masked.symm.trans plain
  have bit := congrFun fixed 0
  simp only [Foundation.Probability.SelectedCouplingGraph.twist] at bit
  cases value : RandomFunctionMACNativeCaller.Backend.tagBits
    (RandomFunctionMACRepresentationGame.publicAnswer out) 0 <;> simp [value] at bit

theorem decoded_full_game (mask : Bool) :
    (fullGame mask).map (RandomFunctionMACRepresentationGame.decode mask) =
      target.run RandomOracle.oracle [] := by
  exact Representation.decoded_run (codec mask) target []


theorem first_three_unaffected : affectedPositions ({7} : Finset (Fin 8)) 3 target = [] := by
  simp [affectedPositions, List.range_succ, first_position, second_position, repeated_position]

/-- The prefix is cut directly from the ORIGINAL complete program, retaining
its actual suspended last query and captured candidate, not a new manual stub. -/
theorem extracted_prefix_patch (saved : Table (Fin 8) (Bits 8)) :
    (pauseAfter 3 target).run (Representation.oracle (codec false)) saved =
      (pauseAfter 3 target).run (Representation.oracle (codec true)) saved := by
  apply pauseAfter_representation_patch (codec false) (codec true) {7} _ 3 target first_three_unaffected
  intro input missing
  exact codec_agrees input (by simpa using missing)

theorem resume_extracted_prefix (mask : Bool) :
    (((pauseAfter 3 target).run (Representation.oracle (codec mask)) []).bind fun past =>
      (past.result.run (Representation.oracle (codec mask)) past.state).map fun last =>
        {last with trace := past.trace ++ last.trace}) = fullGame mask :=
  pauseAfter_continuation 3 target (Representation.oracle (codec mask)) []

end Foundation.Symmetric.RandomFunctionMACQueryFootprint
