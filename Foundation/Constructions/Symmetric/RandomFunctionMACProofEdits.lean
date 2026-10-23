import Foundation.Crypto.Logic.Polygraph.OracleLocalEdits
import Foundation.Constructions.Symmetric.RandomFunctionMACProofSyntax

/-! Two proof routes for an adaptive MAC, using a restricted edit language.
The ideal bound below is reconstructed from a cache/history invariant and
the one-call fresh-guess lemma, not from `secure` or `fresh_guess_bound`.
The extracted oracle program is identified syntactically, so the query bound
applies to the actual distinguisher. Native machine time remains separate.
-/
namespace Foundation.Symmetric.RandomFunctionMACProofEdits
open Foundation.Probability CryptoOracle CryptoOracle.ProofEdits
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

variable {Input Tag : Type} [DecidableEq Input] [DecidableEq Tag]

/-- Construct the route comparison recursively from two local rule schemata.
No probability, semantic equality or finished MAC theorem is an argument. -/
noncomputable def routes (attack : Program Input Tag (Input × Tag)) : Edit (before attack) (after attack) := by
  induction attack with
  | done result =>
      rcases result with ⟨message, guess⟩
      exact .freshQuery message message (fun fresh tag => .done (fresh && decide (tag = guess)))
  | query message next ih =>
      exact .trans (.recordQuery message message (fun tag => before (next tag)))
        (.query message (fun tag => .record message (ih tag)))
  | coin next ih => exact .coin ih

noncomputable def cachedRoutes (attack : Program Input Tag (Input × Tag)) :
    Edit (before attack) (cached attack) :=
  .trans (routes attack) (after attack).rememberEdit

/-- Fully expanded route certificates. Their syntax has no whole-suffix
primitive; empty facts impose no restriction on the initial cache. -/
noncomputable def localRoutes (attack : Program Input Tag (Input × Tag)) :
    LocalEdit [] (before attack) (after attack) := (routes attack).expand []

noncomputable def localCachedRoutes (attack : Program Input Tag (Input × Tag)) :
    LocalEdit [] (before attack) (cached attack) := (cachedRoutes attack).expand []

/-- Full instrumentation equation: the history contains signing requests
only, while the public trace additionally contains the final verification
call. Both the final cache and response-dependent forgery are retained. -/
theorem before_full (attack : Program Input Tag (Input × Tag))
    (world : Oracle Input Tag (RandomOracle.Table Input Tag))
    (signed : List Input) (table : RandomOracle.Table Input Tag) :
    (before attack).run world signed table =
      (attack.run world table).bind (fun out =>
        (world out.state out.result.1).map (fun answer =>
          (⟨(decide (out.result.1 ∉ signed ++ out.trace.map Prod.fst) &&
              decide (answer.2 = out.result.2), signed ++ out.trace.map Prod.fst),
            answer.1, out.trace ++ [(out.result.1, answer.2)]⟩ :
              Outcome Input Tag (Bool × List Input) (RandomOracle.Table Input Tag)))) := by
  induction attack generalizing signed table with
  | done result =>
      rcases result with ⟨message, guess⟩
      simp [before, Command.run, Command.compile, Program.run, PMF.map, Function.comp_def]
  | coin next ih =>
      simp only [before, Command.run, Command.compile, Program.run, PMF.bind_bind]
      congr 1
      funext bit
      exact ih bit signed table
  | query message next ih =>
      simp only [before, Command.run, Command.compile, Program.run, PMF.bind_map,
        PMF.bind_bind]
      congr 1
      funext answer
      have tail := ih answer.2 (signed ++ [message]) answer.1
      change ((before (next answer.2)).run world (signed ++ [message]) answer.1).map _ = _
      rw [tail]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, List.map_cons,
        List.append_assoc, List.cons_append, List.nil_append]

/-- Every cached message was signed. This assertion is needed only before
the final verification query; verification may cache an unsigned message. -/
def Covered (table : RandomOracle.Table Input Tag) (signed : List Input) : Prop :=
  ∀ entry ∈ table, entry.1 ∈ signed

omit [DecidableEq Tag] in
theorem Covered.fresh {table : RandomOracle.Table Input Tag} {signed : List Input}
    (covered : Covered table signed) (message : Input) (fresh : message ∉ signed) :
    table.lookup message = none := by
  cases known : table.lookup message with
  | none => rfl
  | some tag =>
      obtain ⟨earlier, later, same, _⟩ := List.lookup_eq_some_iff.mp known
      exact False.elim (fresh (covered (message, tag) (by rw [same]; simp)))

omit [DecidableEq Tag] in
theorem Covered.query [Fintype Tag] [Nonempty Tag]
    {table : RandomOracle.Table Input Tag} {signed : List Input}
    (covered : Covered table signed) (message : Input) (answer : RandomOracle.Table Input Tag × Tag)
    (reachable : answer ∈ (RandomOracle.oracle table message).support) :
    Covered answer.1 (signed ++ [message]) := by
  intro entry member
  rcases List.mem_cons.mp (RandomOracle.step_entries table message answer reachable member) with same | old
  · subst entry; simp
  · exact List.mem_append_left _ (covered entry old)

/-- Local terminal rule. The only nonzero probability fact used here is the
uniform response at an input absent from the current cache. -/
theorem verify_bound [Fintype Tag] [Nonempty Tag]
    (message : Input) (guess : Tag) (signed : List Input) (table : RandomOracle.Table Input Tag)
    (covered : Covered table signed) :
    eventProb ((before (.done (message, guess))).run RandomOracle.oracle signed table)
      (fun out => out.result.1 = true) ≤ (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  simp only [before, Command.run, Command.compile, Program.run, PMF.pure_map]
  change eventProb ((RandomOracle.oracle table message).map (fun answer =>
    (⟨(decide (message ∉ signed) && decide (answer.2 = guess), signed), answer.1,
      [(message, answer.2)]⟩ : Outcome Input Tag (Bool × List Input) (RandomOracle.Table Input Tag))))
      (fun out => out.result.1 = true) ≤ _
  rw [eventProb_map]
  by_cases fresh : message ∉ signed
  · have terminal := RandomOracle.fresh_guess table message guess (covered.fresh message fresh)
    rw [eventProb_map] at terminal
    simpa [fresh] using terminal.le
  · simp [fresh, eventProb]

/-- Arbitrary adaptive signing, repeated requests and attacker coins preserve
the same bound. The induction maintains the shared cache/history assertion. -/
theorem before_bound [Fintype Tag] [Nonempty Tag]
    (attack : Program Input Tag (Input × Tag)) (signed : List Input)
    (table : RandomOracle.Table Input Tag) (covered : Covered table signed) :
    eventProb ((before attack).run RandomOracle.oracle signed table)
      (fun out => out.result.1 = true) ≤ (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  induction attack generalizing signed table with
  | done result =>
      rcases result with ⟨message, guess⟩
      exact verify_bound message guess signed table covered
  | query message next ih =>
      simp only [before, Command.run, Command.compile, Program.run]
      apply eventProb_bind_le_of_support
      intro answer reachable
      rw [eventProb_map]
      exact ih answer.2 (signed ++ [message]) answer.1 (covered.query message answer reachable)
  | coin next ih =>
      simp only [before, Command.run, Command.compile, Program.run]
      apply eventProb_bind_le_of_support
      intro bit _
      exact ih bit signed table covered

theorem after_bound [Fintype Tag] [Nonempty Tag]
    (attack : Program Input Tag (Input × Tag)) (signed : List Input)
    (table : RandomOracle.Table Input Tag) (covered : Covered table signed) :
    eventProb ((after attack).run RandomOracle.oracle signed table)
      (fun out => out.result.1 = true) ≤ (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  rw [← (localRoutes attack).sound RandomOracle.oracle lazy_cache_laws signed table (knows_nil table)]
  exact before_bound attack signed table covered

theorem cached_bound [Fintype Tag] [Nonempty Tag]
    (attack : Program Input Tag (Input × Tag)) (signed : List Input)
    (table : RandomOracle.Table Input Tag) (covered : Covered table signed) :
    eventProb ((cached attack).run RandomOracle.oracle signed table)
      (fun out => out.result.1 = true) ≤ (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  rw [← (localCachedRoutes attack).sound RandomOracle.oracle lazy_cache_laws signed table (knows_nil table)]
  exact before_bound attack signed table covered

theorem compile_before (attack : Program Input Tag (Input × Tag)) (signed : List Input) :
    ((before attack).compile signed).bind (fun result => .done result.1) =
      RandomFunctionMACSchedules.checkedAttack signed attack := by
  induction attack generalizing signed with
  | done result => rcases result with ⟨message, guess⟩; rfl
  | query message next ih =>
      simp only [before, Command.compile, Program.bind, RandomFunctionMACSchedules.checkedAttack]
      congr 1
      funext tag
      exact ih tag (signed ++ [message])
  | coin next ih =>
      simp only [before, Command.compile, Program.bind, RandomFunctionMACSchedules.checkedAttack]
      congr 1
      funext bit
      exact ih bit signed

theorem distinguisher_eq (attack : Program Input Tag (Input × Tag)) :
    distinguisher attack = RandomFunctionMACSchedules.checkedAttack [] attack :=
  compile_before attack []

theorem distinguisher_queries {attack : Program Input Tag (Input × Tag)} {q : Nat}
    (bound : attack.BoundedQueries q) : (distinguisher attack).BoundedQueries (q + 1) := by
  rw [distinguisher_eq]
  exact RandomFunctionMACSchedules.checkedAttack_queries bound []

theorem distinguisher_result (attack : Program Input Tag (Input × Tag))
    (world : Oracle Input Tag (RandomOracle.Table Input Tag)) (table : RandomOracle.Table Input Tag) :
    ((distinguisher attack).run world table).map Outcome.result =
      ((before attack).run world [] table).map (fun out => out.result.1) := by
  simp [distinguisher, Program.run_bind, Program.run, Command.run, PMF.map, Function.comp_def]

theorem ideal_bound [Fintype Input] [Fintype Tag] [Nonempty Tag]
    (attack : Program Input Tag (Input × Tag)) :
    eventProb (RandomFunctionMACSchedules.idealExperiment (distinguisher attack)) (· = true) ≤
      (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  unfold RandomFunctionMACSchedules.idealExperiment
  rw [← PMF.map_bind, RandomOracle.eager_lazy]
  rw [distinguisher_result, eventProb_map]
  exact before_bound attack [] [] (by intro entry member; cases member)

theorem keyed_bound [Fintype Input] [Fintype Tag] [Nonempty Tag]
    {Key : Type} (keys : PMF Key) (evaluate : Key → Input → Tag)
    (attack : Program Input Tag (Input × Tag)) (epsilon : ℝ≥0∞)
    (prf : eventProb (RandomFunctionMACSchedules.familyExperiment keys evaluate
        (distinguisher attack)) (· = true) ≤
      eventProb (RandomFunctionMACSchedules.idealExperiment (distinguisher attack)) (· = true) + epsilon) :
    eventProb (RandomFunctionMACSchedules.keyedGame keys evaluate attack) (· = true) ≤
      epsilon + (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  have reduction := prf
  rw [distinguisher_eq] at reduction
  change eventProb (RandomFunctionMACSchedules.keyedGame keys evaluate attack) (· = true) ≤ _ at reduction
  calc
    _ ≤ eventProb (RandomFunctionMACSchedules.idealExperiment (distinguisher attack))
        (· = true) + epsilon := by simpa only [distinguisher_eq] using reduction
    _ ≤ (Fintype.card Tag : ℝ≥0∞)⁻¹ + epsilon := add_le_add (ideal_bound attack) le_rfl
    _ = _ := add_comm _ _

theorem after_queries {attack : Program Input Tag (Input × Tag)} {q : Nat}
    (bound : attack.BoundedQueries q) (signed : List Input) :
    ((after attack).compile signed).BoundedQueries (q + 1) := by
  induction bound generalizing signed with
  | done result q =>
      rcases result with ⟨message, guess⟩
      exact .query _ _ q (fun _ => .done _ q)
  | query message next q bounds ih =>
      exact .query _ _ (q + 1) (fun tag => ih tag (signed ++ [message]))
  | coin next q bounds ih => exact .coin _ _ (fun bit => ih bit signed)

theorem cachedDistinguisher_queries {attack : Program Input Tag (Input × Tag)} {q : Nat}
    (bound : attack.BoundedQueries q) : (cachedDistinguisher attack).BoundedQueries (q + 1) := by
  have compiled := (after attack).remember_queries [] (after_queries bound [])
  simpa only [cachedDistinguisher, cached, Command.finish, Nat.add_zero] using
    compiled.bind (fun result => .done result.1)
    (fun _ => .done _ 0)

/-- The actual extracted program implements the original MAC game for each
key distribution, including its cache-dependent proof edits. -/
theorem cached_family_eq {Key : Type} (keys : PMF Key) (evaluate : Key → Input → Tag)
    (attack : Program Input Tag (Input × Tag)) :
    RandomFunctionMACSchedules.familyExperiment keys evaluate (cachedDistinguisher attack) =
      RandomFunctionMACSchedules.keyedGame keys evaluate attack := by
  unfold RandomFunctionMACSchedules.familyExperiment RandomFunctionMACSchedules.keyedGame
  congr 1
  funext key
  rw [cachedDistinguisher, Command.finish_result]
  rw [← (localCachedRoutes attack).sound (RandomOracle.eager (evaluate key)) (eager_cache_laws _)
    [] [] (knows_nil [])]
  rw [← distinguisher_result, distinguisher_eq]

theorem cached_ideal_bound [Fintype Input] [Fintype Tag] [Nonempty Tag]
    (attack : Program Input Tag (Input × Tag)) :
    eventProb (RandomFunctionMACSchedules.idealExperiment (cachedDistinguisher attack)) (· = true) ≤
      (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  unfold RandomFunctionMACSchedules.idealExperiment
  simp_rw [cachedDistinguisher, Command.finish_result]
  rw [← PMF.map_bind, (localCachedRoutes attack).symm.sampling_square [] [] (knows_nil []), eventProb_map]
  exact before_bound attack [] [] (by intro entry member; cases member)

theorem cached_keyed_bound [Fintype Input] [Fintype Tag] [Nonempty Tag]
    {Key : Type} (keys : PMF Key) (evaluate : Key → Input → Tag)
    (attack : Program Input Tag (Input × Tag)) (epsilon : ℝ≥0∞)
    (prf : eventProb (RandomFunctionMACSchedules.familyExperiment keys evaluate
        (cachedDistinguisher attack)) (· = true) ≤
      eventProb (RandomFunctionMACSchedules.idealExperiment (cachedDistinguisher attack))
        (· = true) + epsilon) :
    eventProb (RandomFunctionMACSchedules.keyedGame keys evaluate attack) (· = true) ≤
      epsilon + (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  rw [cached_family_eq] at prf
  calc
    _ ≤ _ := prf
    _ ≤ (Fintype.card Tag : ℝ≥0∞)⁻¹ + epsilon := add_le_add (cached_ideal_bound attack) le_rfl
    _ = _ := add_comm _ _

end Foundation.Symmetric.RandomFunctionMACProofEdits
