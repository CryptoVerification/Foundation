import Foundation.Crypto.Meta.Polygraph.OracleInteractionCertificate
import Foundation.Constructions.Symmetric.RandomFunctionMACNativeCaller
import Foundation.Examples.RandomFunctionMACPosterior
import Foundation.Examples.OracleInteractionBaseline

/-! A mixed diagram inside the SAME adaptive MAC: after the actual first
two signing queries, move refresh of unqueried message 7 across recording
and the repeated signing query. Retain the full state and final verification.
The finite-function refresh is a proof operation, not a caller instruction.
-/
namespace Foundation.Symmetric.RandomFunctionMACInteraction
open Foundation.Probability CryptoOracle CryptoOracle.RandomOracle
open CryptoOracle.ProofEdits CryptoOracle.ProofEdits.Interaction
open RandomFunctionMACNativeCaller (firstMessage secondMessage)
open RandomFunctionMACPosterior (Avoids avoids_trace)
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
abbrev Message := Fin 8
abbrev Tag := Fin 256
abbrev Store := State Message Tag

structure Context where
  coin : Bool
  first : Tag
  second : Tag

def initialProgram : Program Message Tag Context :=
  .coin fun coin => .query (firstMessage coin) fun first =>
    .query (secondMessage first) fun second => .done ⟨coin, first, second⟩

theorem attack_decomposition :
    initialProgram.bind (fun context => .query (firstMessage context.coin) fun repeated =>
      .done ((7 : Message), if context.coin then repeated else context.second)) =
      RandomFunctionMACSchedules.Examples.attack := rfl

theorem first_ne_seven (coin : Bool) : firstMessage coin ≠ (7 : Message) := by cases coin <;> decide

theorem second_ne_seven (tag : Tag) : secondMessage tag ≠ (7 : Message) := by
  by_cases even : tag.val % 2 = 0 <;> simp [secondMessage, even]

theorem prefix_avoids : Avoids 7 initialProgram := by
  simp only [initialProgram, Avoids]
  exact fun coin => ⟨first_ne_seven coin, fun first => ⟨second_ne_seven first, fun _ => trivial⟩⟩

noncomputable def prefixLaw : PMF (Context × Store) :=
  (uniform (Message → Tag)).bind fun function =>
    (initialProgram.run (eager function) []).map fun out =>
      (out.result, ⟨out.state, out.trace.map Prod.fst, out.trace.reverse, function⟩)

theorem prefix_invariant (pair : Context × Store) (supported : pair ∈ prefixLaw.support) :
    Known (pair.2.cache.map Prod.fst).toFinset pair.2 ∧ Coherent pair.2 ∧ pair.2.cache.lookup 7 = none := by
  rw [prefixLaw, PMF.mem_support_bind_iff] at supported
  obtain ⟨function, _, supported⟩ := supported
  rw [PMF.mem_support_map_iff] at supported
  obtain ⟨out, selected, rfl⟩ := supported
  refine ⟨known_cache _, ?_, ?_⟩
  · exact Cube.eager_run_values function initialProgram out selected
  · have reachable := eager_run_support function initialProgram [] out selected
    exact unqueried_fresh initialProgram out reachable 7 (avoids_trace initialProgram 7 prefix_avoids oracle [] out reachable)

theorem prefix_unsigned (pair : Context × Store) (supported : pair ∈ prefixLaw.support) :
    (7 : Message) ∉ pair.2.signed := by
  rw [prefixLaw, PMF.mem_support_bind_iff] at supported
  obtain ⟨function, _, supported⟩ := supported
  rw [PMF.mem_support_map_iff] at supported
  obtain ⟨out, selected, rfl⟩ := supported
  intro member
  obtain ⟨⟨message, tag⟩, included, same⟩ := List.mem_map.mp member
  change message = 7 at same
  subst message
  exact avoids_trace initialProgram 7 prefix_avoids (eager function) [] out selected tag included

def beforeWord (coin : Bool) : List (Action Message) :=
  [.refresh 7, .record (firstMessage coin), .query (firstMessage coin)]

def afterWord (coin : Bool) : List (Action Message) :=
  [.query (firstMessage coin), .record (firstMessage coin), .refresh 7]

def diagram (coin : Bool) : Cell (beforeWord coin) (afterWord coin) :=
  .trans (.exchange (.refresh 7) (.record (firstMessage coin)) rfl [.query (firstMessage coin)])
    (.trans (.cons (.record (firstMessage coin))
        (.exchange (.refresh 7) (.query (firstMessage coin))
          (by simpa only [independent, decide_eq_true_eq] using first_ne_seven coin) []))
      (.exchange (.record (firstMessage coin)) (.query (firstMessage coin)) rfl [.refresh 7]))

theorem validates_fresh (coin : Bool) (seen : Finset Message) (fresh : (7 : Message) ∉ seen) :
    Certificate.validates seen (beforeWord coin) (afterWord coin) [0, 1, 0] = true := by
  have checked : (Certificate.certify (beforeWord coin) (afterWord coin) [0, 1, 0]).isSome = true := by
    cases coin <;> decide
  simp only [Certificate.validates, checked, Bool.and_true]
  cases coin <;> simp [beforeWord, firstMessage, scan, fresh]

def repeatedTag (state : Store) : Tag := ((state.reverseTrace.head?).map Prod.snd).getD 0
def guess (context : Context) (state : Store) : Tag := if context.coin then repeatedTag state else context.second
def reply (state : Store) (message : Message) : Tag := (state.cache.lookup message).getD (state.function message)

noncomputable def finish (context : Context) (state : Store) :
    PMF (Outcome Message Tag Bool Store) :=
  PMF.pure ⟨decide (reply state 7 = guess context state), ask state 7, (ask state 7).reverseTrace.reverse⟩

noncomputable def game (word : Bool → List (Action Message)) : PMF (Outcome Message Tag Bool Store) :=
  prefixLaw.bind fun pair => (Interaction.run (word pair.1.coin) pair.2).bind (finish pair.1)

theorem full_game_eq : game beforeWord = game afterWord := by
  apply bind_congr_of_support
  intro pair supported
  obtain ⟨known, _, fresh⟩ := prefix_invariant pair supported
  have accepted := validates_fresh pair.1.coin _ ((known 7).mp fresh)
  rw [Certificate.validates_kernel _ _ _ _ accepted pair.2]

theorem ordinary_full_game_eq : game beforeWord = game afterWord := by
  unfold game
  congr 1
  funext pair
  simpa only [beforeWord, afterWord] using congrArg (fun law => law.bind (finish pair.1))
    (Baseline.mixed_block (firstMessage pair.1.coin) 7 (first_ne_seven pair.1.coin) pair.2)

theorem retained_context :
    (prefixLaw.bind fun pair => (Interaction.run (beforeWord pair.1.coin) pair.2).map (fun final => (pair, final))) =
      (prefixLaw.bind fun pair => (Interaction.run (afterWord pair.1.coin) pair.2).map (fun final => (pair, final))) := by
  congr 1
  funext pair
  rw [(diagram pair.1.coin).sound pair.2]

def packedSigning (function : Message → Tag) (out : Outcome Message Tag (Message × Tag) (Table Message Tag)) :
    Tag × Store := (out.result.2, ⟨out.state, out.trace.map Prod.fst, out.trace.reverse, function⟩)

noncomputable def rawSigning : PMF (Tag × Store) :=
  (uniform (Message → Tag)).bind fun function =>
    (RandomFunctionMACSchedules.Examples.attack.run (eager function) []).map (packedSigning function)

noncomputable def blockSigning : PMF (Tag × Store) :=
  prefixLaw.map fun pair =>
    let middle := record (ask pair.2 (firstMessage pair.1.coin)) (firstMessage pair.1.coin)
    (guess pair.1 middle, middle)

theorem block_signing_eq : blockSigning = rawSigning := by
  unfold blockSigning rawSigning prefixLaw
  rw [← attack_decomposition]
  simp_rw [Program.run_bind]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  congr 1
  funext function
  simp only [PMF.map, Function.comp_def]
  apply congrArg (PMF.bind (initialProgram.run (eager function) []))
  funext out
  cases cached : out.state.lookup (firstMessage out.result.coin) <;>
    simp [Program.run, eager, cached, packedSigning, guess, repeatedTag, ask, record,
      PMF.map, List.reverse_append]

noncomputable def refreshedSigning : PMF (Tag × Store) :=
  rawSigning.bind fun pair => (resample pair.2 7).map (fun final => (pair.1, final))

/-- This forgets neither the cache nor the full signing transcript. The
refreshed final function has the original eager marginal; its coupling to
the old function is intentionally not identified with the identity. -/
theorem refreshed_signing_eq : refreshedSigning = rawSigning := by
  have refreshed := eager_resample_unqueried RandomFunctionMACSchedules.Examples.attack
    (fun _ => (7 : Message)) RandomFunctionMACPosterior.signing_fresh
  have projected := congrArg (PMF.map (fun pair => packedSigning pair.2 pair.1)) refreshed
  simpa [refreshedSigning, rawSigning, packedSigning, resample, update,
    PMF.map_bind, PMF.bind_map, PMF.bind_bind, PMF.map_comp, Function.comp_def, PMF.map] using projected

noncomputable def verification (pair : Tag × Store) : PMF (Outcome Message Tag Bool Store) :=
  PMF.pure ⟨decide (reply pair.2 7 = pair.1), ask pair.2 7, (ask pair.2 7).reverseTrace.reverse⟩

theorem after_is_refreshed : game afterWord = refreshedSigning.bind verification := by
  rw [refreshedSigning, ← block_signing_eq]
  simp [game, afterWord, blockSigning, Interaction.run, Interaction.step, finish, verification,
    resample, guess, repeatedTag, update, PMF.bind_bind, PMF.map, Function.comp_def]

theorem erase_refresh : game afterWord = rawSigning.bind verification := by
  rw [after_is_refreshed, refreshed_signing_eq]

theorem valid_final_state (pair : Context × Store) (supported : pair ∈ prefixLaw.support)
    (final : Store) (reachable : final ∈ (Interaction.run (afterWord pair.1.coin) pair.2).support) : Coherent final := by
  obtain ⟨known, coherent, fresh⟩ := prefix_invariant pair supported
  exact Certificate.validates_invariant _ _ _ _
    (validates_fresh pair.1.coin _ ((known 7).mp fresh)) pair.2 final known coherent reachable

theorem fresh_finish (context : Context) (state : Store) (fresh : state.cache.lookup 7 = none) :
    eventProb ((resample state 7).bind (finish context)) (fun out => out.result = true) = (256 : ℝ≥0∞)⁻¹ := by
  have projected : ((resample state 7).bind (finish context)).map Outcome.result =
      (uniform Tag).map (fun tag => decide (tag = guess context state)) := by
    simp [resample, finish, reply, guess, repeatedTag, update, fresh,
      Function.comp_def, PMF.map]
  have probability := congrArg (fun law => eventProb law (· = true)) projected
  simpa only [eventProb_map, decide_eq_true_eq, uniform_guess, Fintype.card_fin, Nat.cast_ofNat] using probability

theorem after_probability (context : Context) (state : Store) (fresh : state.cache.lookup 7 = none) :
    eventProb ((Interaction.run (afterWord context.coin) state).bind (finish context)) (fun out => out.result = true) =
      (256 : ℝ≥0∞)⁻¹ := by
  have middleFresh : (record (ask state (firstMessage context.coin)) (firstMessage context.coin)).cache.lookup 7 = none := by
    rw [show (record (ask state (firstMessage context.coin)) (firstMessage context.coin)).cache =
      (ask state (firstMessage context.coin)).cache from rfl]
    rw [ask_lookup_other state _ 7 (Ne.symm (first_ne_seven context.coin))]
    exact fresh
  simpa only [afterWord, Interaction.run, Interaction.step, PMF.pure_bind, PMF.bind_pure] using
    fresh_finish context (record (ask state (firstMessage context.coin)) (firstMessage context.coin)) middleFresh

theorem after_security : eventProb (game afterWord) (fun out => out.result = true) = (256 : ℝ≥0∞)⁻¹ := by
  apply RandomOracle.Posterior.event_bind_constant
  intro pair supported
  exact after_probability pair.1 pair.2 (prefix_invariant pair supported).2.2

theorem before_security : eventProb (game beforeWord) (fun out => out.result = true) = (256 : ℝ≥0∞)⁻¹ := by
  rw [full_game_eq]
  exact after_security

theorem before_original_eq : game beforeWord = rawSigning.bind verification :=
  full_game_eq.trans erase_refresh

theorem original_game_security :
    eventProb (rawSigning.bind verification) (fun out => out.result = true) = (256 : ℝ≥0∞)⁻¹ := by
  rw [← erase_refresh]
  exact after_security

theorem mixed_counts (coin : Bool) :
    queryCount (beforeWord coin) = queryCount (afterWord coin) ∧
      recordCount (beforeWord coin) = recordCount (afterWord coin) ∧
      drawCount (beforeWord coin) = drawCount (afterWord coin) := (diagram coin).counts

theorem after_coherent (out : Outcome Message Tag Bool Store) (supported : out ∈ (game afterWord).support) :
    Coherent out.state := by
  rw [game, PMF.mem_support_bind_iff] at supported
  obtain ⟨pair, reachable, supported⟩ := supported
  rw [PMF.mem_support_bind_iff] at supported
  obtain ⟨final, selected, supported⟩ := supported
  rw [finish, PMF.mem_support_pure_iff] at supported
  subst out
  exact ask_coherent final 7 (valid_final_state pair reachable final selected)

theorem after_unsigned (out : Outcome Message Tag Bool Store) (supported : out ∈ (game afterWord).support) :
    (7 : Message) ∉ out.state.signed := by
  rw [game, PMF.mem_support_bind_iff] at supported
  obtain ⟨pair, reachable, supported⟩ := supported
  rw [PMF.mem_support_bind_iff] at supported
  obtain ⟨final, selected, supported⟩ := supported
  rw [finish, PMF.mem_support_pure_iff] at supported
  subst out
  rw [ask_signed]
  simp only [afterWord, Interaction.run, Interaction.step, PMF.pure_bind, PMF.bind_pure,
    resample, PMF.mem_support_map_iff] at selected
  obtain ⟨tag, _, rfl⟩ := selected
  change (7 : Message) ∉ (record (ask pair.2 (firstMessage pair.1.coin)) (firstMessage pair.1.coin)).signed
  simp only [record, List.mem_append, List.mem_singleton, not_or, ask_signed]
  exact ⟨prefix_unsigned pair reachable, Ne.symm (first_ne_seven pair.1.coin)⟩

theorem refuses_same_coordinate (seen : Finset Message) (target : List (Action Message)) (positions : List Nat) :
    Certificate.validates seen [.query 7, .refresh 7] target positions = false :=
  Certificate.rejects_exposed_refresh seen 7 target positions

end Foundation.Symmetric.RandomFunctionMACInteraction
