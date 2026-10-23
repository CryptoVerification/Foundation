import Foundation.Crypto.Semantics.Oracle.ChangeFrontier
import Foundation.Examples.RandomFunctionMACQueryFootprint

/-! Automatic first-change suspension for the existing four-query MAC caller.
The input-7 edit reaches verification only after the three signing queries. -/
namespace Foundation.Symmetric.RandomFunctionMACChangeFrontier
open Foundation.Probability CryptoOracle CryptoOracle.Program CryptoOracle.RandomOracle
open RandomFunctionMACNativeCaller (target firstMessage secondMessage)
open RandomFunctionMACRepresentationGame (codec)

private theorem first_ne (coin : Bool) : firstMessage coin ≠ 7 := by
  cases coin <;> decide
private theorem second_ne (tag : Fin 256) : secondMessage tag ≠ 7 := by
  unfold secondMessage
  split <;> decide

theorem automatic_cut : pauseBefore ({7} : Finset (Fin 8)) target = pauseAfter 3 target := by
  simp only [target, pauseBefore, pauseAfter]
  congr 1
  funext coin
  simp only [Finset.mem_singleton, first_ne, if_false]
  congr 1
  funext first
  simp only [second_ne, if_false, if_true]

theorem shared_prefix (saved : Table (Fin 8) (Bits 8)) :
    (pauseBefore {7} target).run (Representation.oracle (codec false)) saved =
      (pauseBefore {7} target).run (Representation.oracle (codec true)) saved := by
  apply pauseBefore_same
  intro request untouched state
  apply Representation.oracle_congr_at
  exact RandomFunctionMACQueryFootprint.codec_agrees request (by simpa using untouched)

/-- The caller always reaches input 7: a generic bad-event bound here is
vacuous. A useful repair must prove a suffix law instead. -/
theorem always_reaches_change (world : Oracle (Fin 8) (Fin 256) (Table (Fin 8) (Bits 8)))
    (saved : Table (Fin 8) (Bits 8)) :
    eventProb ((pauseBefore {7} target).run world saved) atChanged = 1 := by
  have all : ∀ past ∈ ((pauseBefore {7} target).run world saved).support, atChanged past := by
    intro past reachable
    rw [automatic_cut] at reachable
    simp only [target, pauseAfter, Program.run] at reachable
    rw [PMF.mem_support_bind_iff] at reachable
    obtain ⟨coin, _, reachable⟩ := reachable
    rw [PMF.mem_support_bind_iff] at reachable
    obtain ⟨first, _, reachable⟩ := reachable
    rw [PMF.mem_support_map_iff] at reachable
    obtain ⟨tail, reachable, rfl⟩ := reachable
    rw [PMF.mem_support_bind_iff] at reachable
    obtain ⟨second, _, reachable⟩ := reachable
    rw [PMF.mem_support_map_iff] at reachable
    obtain ⟨tail, reachable, rfl⟩ := reachable
    rw [PMF.mem_support_bind_iff] at reachable
    obtain ⟨repeated, _, reachable⟩ := reachable
    rw [PMF.mem_support_map_iff] at reachable
    obtain ⟨last, reachable, rfl⟩ := reachable
    rw [PMF.mem_support_pure_iff] at reachable
    subst last
    exact ⟨7, _, rfl⟩
  have same := eventProb_congr_of_support ((pauseBefore {7} target).run world saved)
    (event := atChanged) (other := fun _ => True) (fun past support => ⟨fun _ => trivial, fun _ => all past support⟩)
  rw [same]
  simp [eventProb, PMF.toOuterMeasure_apply]

private theorem decoded_resume (mask : Bool)
    (past : Outcome (Fin 8) (Fin 256) (Program (Fin 8) (Fin 256) Bool) (Table (Fin 8) (Fin 256))) :
    (resumePast (Representation.oracle (codec mask))
      (mapState (Representation.table (codec mask)) past)).map (RandomFunctionMACRepresentationGame.decode mask) =
      resumePast RandomOracle.oracle past := by
  have law := Representation.decoded_run (codec mask) past.result past.state
  have mapped := congrArg (fun p => p.map (fun last => {last with trace := past.trace ++ last.trace})) law
  simpa only [resumePast, mapState, RandomFunctionMACRepresentationGame.decode,
    PMF.map_comp, Function.comp_def] using mapped

/-- The obligation at every actually reached frontier compares decoded FULL
suffix outcomes. It uses the real captured candidate and shared signing cache. -/
theorem local_decoded_repair
    (past : Outcome (Fin 8) (Fin 256) (Program (Fin 8) (Fin 256) Bool) (Table (Fin 8) (Bits 8)))
    (reachable : past ∈ ((pauseBefore {7} target).run (Representation.oracle (codec false)) []).support) :
    (resumePast (Representation.oracle (codec false)) past).map (RandomFunctionMACRepresentationGame.decode false) =
      (resumePast (Representation.oracle (codec true)) past).map (RandomFunctionMACRepresentationGame.decode true) := by
  have encoded := Representation.run (codec false) (pauseBefore {7} target) []
  simp only [Representation.table, List.map_nil] at encoded
  rw [← encoded, PMF.mem_support_map_iff] at reachable
  obtain ⟨plain, supported, rfl⟩ := reachable
  have disjoint : Disjoint (pauseBefore ({7} : Finset (Fin 8)) target).footprint {7} := by
    rw [automatic_cut]
    exact pauseAfter_unaffected 3 target {7} RandomFunctionMACQueryFootprint.first_three_unaffected
  generalize prefix_eq : pauseBefore ({7} : Finset (Fin 8)) target = prefixProgram at supported disjoint
  have states : Representation.table (codec false) plain.state = Representation.table (codec true) plain.state := by
    apply Representation.table_eq_of_agree
    intro input response member
    have effect := Representation.plain_entries_in_set prefixProgram
      prefixProgram.footprint (fun _ h => h) plain supported (input, response) member
    apply RandomFunctionMACQueryFootprint.codec_agrees
    intro same
    exact Finset.disjoint_left.mp disjoint effect (by simp [same])
  have pasts : mapState (Representation.table (codec false)) plain =
      mapState (Representation.table (codec true)) plain := by
    simp only [mapState, states]
  rw [decoded_resume false, pasts, decoded_resume true]

/-- Assemble the complete decoded-game repair from the local frontier laws. -/
theorem assembled_decoded_repair :
    (target.run (Representation.oracle (codec false)) []).map (RandomFunctionMACRepresentationGame.decode false) =
      (target.run (Representation.oracle (codec true)) []).map (RandomFunctionMACRepresentationGame.decode true) := by
  apply repair_observation_at_frontier {7} target
  · intro request untouched state
    exact Representation.oracle_congr_at _ _ request
      (RandomFunctionMACQueryFootprint.codec_agrees request (by simpa using untouched)) state
  · exact local_decoded_repair

end Foundation.Symmetric.RandomFunctionMACChangeFrontier
