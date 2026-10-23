import Foundation.Constructions.Symmetric.RandomFunctionMACProofEdits
import Foundation.Examples.ScheduleCertificate
import Foundation.Crypto.Logic.Polygraph.OracleLocalCells

/-! Positive and negative checks for the restricted oracle edit language.
The ordinary comparison is intentionally allowed to share lemmas and use
induction. For the initial two routes it even proves syntactic equality after
history compilation, so this example does not establish a higher-dimensional
proof-size advantage. -/
namespace CryptoOracle.ProofEdits.Examples
open Foundation.Probability
open Foundation.Symmetric.RandomFunctionMACProofEdits
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Fair baseline: no route enumeration, and no restriction on lemma sharing.
The first history-moving routes collapse already during compilation. -/
theorem ordinary_compile_eq {Input Tag : Type} [DecidableEq Input] [DecidableEq Tag]
    (attack : Program Input Tag (Input × Tag)) (signed : List Input) :
    (before attack).compile signed = (after attack).compile signed := by
  induction attack generalizing signed with
  | done result => rcases result with ⟨message, guess⟩; rfl
  | query message next ih =>
      simp only [before, after, Command.compile]
      congr 1
      funext tag
      exact ih tag (signed ++ [message])
  | coin next ih =>
      simp only [before, after, Command.compile]
      congr 1
      funext bit
      exact ih bit signed

abbrev attack := Foundation.Symmetric.RandomFunctionMACSchedules.Examples.attack

/-- The adaptive three-signing-query example includes a repeated message,
coins, and response-dependent selection of its second message. Both routes
retain the cache, full trace and signing history, plus the residual function. -/
theorem adaptive_posterior_square :
    (uniform (Fin 8 → Fin 256)).bind (fun function =>
      ((before attack).run (RandomOracle.eager function) [] []).map
        (fun out => (out, RandomOracle.complete [] function))) =
    ((after attack).run RandomOracle.oracle [] []).bind (fun out =>
      (uniform (Fin 8 → Fin 256)).map (fun function =>
        (out, RandomOracle.complete out.state function))) :=
  (routes attack).posterior_square [] []

theorem adaptive_ideal_bound :
    eventProb ((after attack).run RandomOracle.oracle [] []) (fun out => out.result.1 = true) ≤
      (256 : ℝ≥0∞)⁻¹ :=
  by simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    after_bound attack [] [] (by intro entry member; cases member)

theorem adaptive_reduction_queries : (distinguisher attack).BoundedQueries 4 :=
  distinguisher_queries Foundation.Symmetric.RandomFunctionMACSchedules.Examples.attack_queries

theorem cached_adaptive_posterior_square :
    (uniform (Fin 8 → Fin 256)).bind (fun function =>
      ((before attack).run (RandomOracle.eager function) [] []).map
        (fun out => (out, RandomOracle.complete [] function))) =
    ((cached attack).run RandomOracle.oracle [] []).bind (fun out =>
      (uniform (Fin 8 → Fin 256)).map (fun function =>
        (out, RandomOracle.complete out.state function))) :=
  (cachedRoutes attack).posterior_square [] []

theorem cached_adaptive_bound :
    eventProb ((cached attack).run RandomOracle.oracle [] []) (fun out => out.result.1 = true) ≤
      (256 : ℝ≥0∞)⁻¹ := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    cached_bound attack [] [] (by intro entry member; cases member)

theorem cached_adaptive_reduction_queries : (cachedDistinguisher attack).BoundedQueries 4 :=
  cachedDistinguisher_queries Foundation.Symmetric.RandomFunctionMACSchedules.Examples.attack_queries

/-- A concrete use of the cache-dependent rule. Both actual lookups remain
in the program; replacing the second response by the first is justified. -/
def repeatedEdit (message : Fin 8) : Edit (Tag := Fin 256)
    (.query message (fun first => .query message (fun second =>
      .done (first, second))))
    (.query message (fun first => .query message (fun _ => .done (first, first)))) :=
  .repeatQuery message (fun first second => .done (first, second))

def testBeforeRecord : Command (Fin 1) Bool Bool :=
  .fresh 0 (fun fresh => .record 0 (.done fresh))

def testAfterRecord : Command (Fin 1) Bool Bool :=
  .record 0 (.fresh 0 (fun fresh => .done fresh))

/-- The disequality condition of `freshRecord` cannot simply be dropped.
This also rules out any derivation using all the other restricted rules. -/
theorem cannot_move_test_across_same_record :
    ¬ Nonempty (Edit testBeforeRecord testAfterRecord) := by
  rintro ⟨edit⟩
  have law := edit.sound (RandomOracle.eager (fun _ : Fin 1 => true))
    (eager_cache_laws _) [] []
  have projected := congrArg (PMF.map (fun out => out.result.1)) law
  have wrong : PMF.pure true = PMF.pure false := by
    simpa [testBeforeRecord, testAfterRecord, Command.run, Command.compile, Program.run,
      PMF.pure_map] using projected
  have member : true ∈ (PMF.pure true).support := by simp
  rw [wrong] at member
  simp at member

/-- Dropping the cache/history assertion is unsound: an unsigned message
with a preloaded known tag is forged with probability one. -/
theorem uncovered_success :
    eventProb ((before (.done (0, true) : Program (Fin 1) Bool (Fin 1 × Bool))).run
      RandomOracle.oracle [] [(0, true)]) (fun out => out.result.1 = true) = 1 := by
  simp [before, Command.run, Command.compile, Program.run, RandomOracle.oracle,
    PMF.pure_map, eventProb]

theorem uncovered_not_bounded :
    ¬ eventProb ((before (.done (0, true) : Program (Fin 1) Bool (Fin 1 × Bool))).run
      RandomOracle.oracle [] [(0, true)]) (fun out => out.result.1 = true) ≤ (2 : ℝ≥0∞)⁻¹ := by
  rw [uncovered_success]
  norm_num

/-- Three calls, with another message between the two calls at message zero. -/
def separatedRepeat : Command (Fin 2) Bool Bool :=
  .query 0 (fun _ => .query 1 (fun _ => .query 0 (fun response => .done response)))

/-- Deliberately not a cache: the first response is false and later ones are
true, including repeats. This is a negative control, not a random oracle. -/
noncomputable def forgetful : Oracle (Fin 2) Bool (RandomOracle.Table (Fin 2) Bool) :=
  fun table request => PMF.pure (((request, !table.isEmpty) :: table), !table.isEmpty)

theorem recall_needs_cache :
    separatedRepeat.run forgetful [] [] ≠ separatedRepeat.remember.run forgetful [] [] := by
  intro equal
  have projected := congrArg (PMF.map (fun out => out.result.1)) equal
  have wrong : PMF.pure true = PMF.pure false := by
    simpa [separatedRepeat, forgetful, Command.remember, Command.recall, Command.run,
      Command.compile, Program.run, PMF.pure_bind, PMF.pure_map] using projected
  have member : true ∈ (PMF.pure true).support := by simp
  rw [wrong] at member
  simp at member

/-- Unlike moving private history updates, the cache-dependent edit cannot
be justified just by compiling the two programs to identical syntax. -/
theorem recall_compile_ne :
    separatedRepeat.compile [] ≠ separatedRepeat.remember.compile [] := by
  intro equal
  exact recall_needs_cache (congrArg (Program.run forgetful []) equal)

/-- The adaptive example now uses an expanded certificate with no suffix
transformation among its elementary generators. -/
theorem elementary_adaptive_posterior_square :
    (uniform (Fin 8 → Fin 256)).bind (fun function =>
      ((before attack).run (RandomOracle.eager function) [] []).map
        (fun out => (out, RandomOracle.complete [] function))) =
    ((cached attack).run RandomOracle.oracle [] []).bind (fun out =>
      (uniform (Fin 8 → Fin 256)).map (fun function =>
        (out, RandomOracle.complete out.state function))) :=
  (localCachedRoutes attack).posterior_square [] [] (knows_nil [])

def separatedElementary : LocalEdit [] separatedRepeat separatedRepeat.remember :=
  separatedRepeat.rememberLocalEdit []

/-- Observations form a conjunction. A later observation never silently
overwrites a conflicting earlier observation in the proof context. -/
theorem conflicting_facts_unreachable (table : RandomOracle.Table (Fin 1) Bool) :
    ¬ Knows [(0, false), (0, true)] table := by
  intro valid
  have first := valid 0 false (by simp)
  have second := valid 0 true (by simp)
  rw [first] at second
  cases second

def unknownResponse : Command (Fin 1) Bool Bool := .query 0 Command.done
def forcedResponse : Command (Fin 1) Bool Bool := .query 0 (fun _ => .done true)

/-- With empty facts the elementary system cannot substitute an arbitrary
response, even though the corresponding rule is available under a fact. -/
theorem cannot_force_unknown_response : ¬ Nonempty (LocalEdit [] unknownResponse forcedResponse) := by
  rintro ⟨edit⟩
  have law := edit.sound (RandomOracle.eager (fun _ : Fin 1 => false))
    (eager_cache_laws _) [] [] (knows_nil [])
  have projected := congrArg (PMF.map (fun out => out.result.1)) law
  have wrong : PMF.pure false = PMF.pure true := by
    simpa [unknownResponse, forcedResponse, Command.run, Command.compile, Program.run,
      RandomOracle.eager, PMF.pure_bind, PMF.pure_map] using projected
  have member : false ∈ (PMF.pure false).support := by simp
  rw [wrong] at member
  simp at member

def force_known_response : LocalEdit [(0, true)] unknownResponse forcedResponse :=
  .cachedQuery [(0, true)] 0 true (by simp) Command.done

/-- Two editing orders under an observed response. The first query creates
the required fact, so the entire diagram is closed under empty facts. -/
def recordThenCache : LocalEdit ([] : List (Fin 2 × Bool))
    (.query 0 (fun _ : Bool => .record 0 (.query 0 Command.done)))
    (.query 0 (fun tag => .query 0 (fun _ => .record 0 (.done tag)))) :=
  .query [] 0 (fun tag => .recordCachedLeft [(0, tag)] 0 0 tag (by simp) Command.done)

def cacheThenRecord : LocalEdit ([] : List (Fin 2 × Bool))
    (.query 0 (fun _ : Bool => .record 0 (.query 0 Command.done)))
    (.query 0 (fun tag => .query 0 (fun _ => .record 0 (.done tag)))) :=
  .query [] 0 (fun tag => .recordCachedRight [(0, tag)] 0 0 tag (by simp) Command.done)

def record_cache_cell : LocalCell recordThenCache cacheThenRecord :=
  .query [] 0 (fun tag => .recordCached [(0, tag)] 0 0 tag (by simp) Command.done)

theorem record_cache_joint :
    (LocalGames.path recordThenCache RandomOracle.oracle lazy_cache_laws [] [] (knows_nil [])
      (fun out => out.result.1 = true)).joint =
    (LocalGames.path cacheThenRecord RandomOracle.oracle lazy_cache_laws [] [] (knows_nil [])
      (fun out => out.result.1 = true)).joint :=
  LocalGames.cell_joint record_cache_cell RandomOracle.oracle lazy_cache_laws [] [] (knows_nil [])
    (fun out => out.result.1 = true)

end CryptoOracle.ProofEdits.Examples
