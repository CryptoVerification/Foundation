import Foundation.Logic.Polygraph.ScheduleCertificate
import Foundation.Crypto.Logic.Polygraph.RandomOracle
import Foundation.Crypto.Semantics.Oracle.RandomOracleGuessing
import Foundation.Crypto.Semantics.Oracle.Composition

/-! A concrete cryptographic use of schedule certificates: chosen-message
unforgeability of the ideal random-function MAC. A key is a uniform finite
function, signing evaluates it, and a forgery must name an unsigned message.
The adversary is adaptive, may repeat queries, and may use local coins.
All permutations of private exposure operations are certified together.
This is an ideal MAC, not a PRF construction or a polynomial-size key claim. -/
namespace Foundation.Symmetric.RandomFunctionMACSchedules

open Foundation.Probability Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.ScheduleCertificate
open CryptoOracle CryptoOracle.RandomOracle
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {Input Tag : Type} [DecidableEq Input] [DecidableEq Tag]
  [Fintype Input] [Fintype Tag] [Nonempty Tag]

/-- Complete the actual attack with one verification query. The signed list
is private game instrumentation, and is not passed to the adversary. -/
def checkedAttack (signed : List Input) : Program Input Tag (Input × Tag) → Program Input Tag Bool
  | .done (message, guess) => .query message (fun tag =>
      .done (decide (message ∉ signed) && decide (tag = guess)))
  | .query message next => .query message (fun tag =>
      checkedAttack (signed ++ [message]) (next tag))
  | .coin next => .coin (fun bit => checkedAttack signed (next bit))

omit [Fintype Input] [Fintype Tag] [Nonempty Tag] in
theorem checkedAttack_queries {attack : Program Input Tag (Input × Tag)} {q : Nat}
    (bound : attack.BoundedQueries q) (signed : List Input) :
    (checkedAttack signed attack).BoundedQueries (q + 1) := by
  induction bound generalizing signed with
  | done result q =>
      rcases result with ⟨message, guess⟩
      exact .query _ _ q (fun _ => .done _ q)
  | query message next q bounds ih =>
      exact .query _ _ (q + 1) (fun tag => ih tag (signed ++ [message]))
  | coin next q bounds ih => exact .coin _ _ (fun bit => ih bit signed)

omit [Fintype Input] [Fintype Tag] [Nonempty Tag] in
theorem checkedAttack_run {State : Type} (world : Oracle Input Tag State)
    (attack : Program Input Tag (Input × Tag)) (signed : List Input) (state : State) :
    ((checkedAttack signed attack).run world state).map Outcome.result =
      (attack.run world state).bind (fun out =>
        (world out.state out.result.1).map (fun answer =>
          decide (out.result.1 ∉ signed ++ out.trace.map Prod.fst) &&
            decide (answer.2 = out.result.2))) := by
  induction attack generalizing signed state with
  | done result =>
      rcases result with ⟨message, guess⟩
      simp [checkedAttack, Program.run, Function.comp_def, PMF.map]
  | query message next ih =>
      simp only [checkedAttack, Program.run, PMF.map_bind, PMF.bind_map, PMF.bind_bind, PMF.map_comp,
        Function.comp_def]
      congr 1
      funext answer
      simpa only [List.map_cons, List.append_assoc, List.singleton_append] using
        ih answer.2 (signed ++ [message]) answer.1
  | coin next ih =>
      simp only [checkedAttack, Program.run, PMF.map_bind, PMF.bind_bind]
      congr 1
      funext bit
      exact ih bit signed state

omit [Fintype Input] in
theorem checked_lazy (attack : Program Input Tag (Input × Tag)) :
    ((checkedAttack [] attack).run oracle []).map Outcome.result = freshGuessGame attack := by
  simpa only [List.nil_append, freshGuessGame] using checkedAttack_run oracle attack [] []

/-- The ordinary ideal MAC game: sample a secret random function, answer
chosen-message signing queries, and verify the final fresh-message guess. -/
noncomputable def game (attack : Program Input Tag (Input × Tag)) : PMF Bool :=
  (uniform (Input → Tag)).bind fun key =>
    ((checkedAttack [] attack).run (eager key) []).map Outcome.result

theorem game_lazy (attack : Program Input Tag (Input × Tag)) :
    game attack = freshGuessGame attack := by
  rw [game, ← PMF.map_bind, eager_lazy, checked_lazy]

theorem secure (attack : Program Input Tag (Input × Tag)) :
    eventProb (game attack) (· = true) ≤ (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  rw [game_lazy]
  exact fresh_guess_bound attack

/-- A pseudorandom-function distinguishing experiment. The challenger uses
a function from the keyed family; the distinguisher only gets query access. -/
noncomputable def familyExperiment {Key : Type} (keys : PMF Key)
    (evaluate : Key → Input → Tag) (distinguisher : Program Input Tag Bool) : PMF Bool :=
  keys.bind fun key => (distinguisher.run (eager (evaluate key)) []).map Outcome.result

noncomputable def idealExperiment (distinguisher : Program Input Tag Bool) : PMF Bool :=
  (uniform (Input → Tag)).bind fun function =>
    (distinguisher.run (eager function) []).map Outcome.result

/-- The ordinary MAC from the supplied keyed function family. The reduction
includes the final verification call, as well as every signing call. -/
noncomputable def keyedGame {Key : Type} (keys : PMF Key) (evaluate : Key → Input → Tag)
    (attack : Program Input Tag (Input × Tag)) : PMF Bool :=
  familyExperiment keys evaluate (checkedAttack [] attack)

/-- Standard concrete PRF-to-MAC reduction for the explicit distinguisher.
`prf` is the one-sided consequence of its PRF distinguishing bound; it is
not supplied as a MAC security assumption. No CPU-time claim is implicit. -/
theorem keyed_secure {Key : Type} (keys : PMF Key) (evaluate : Key → Input → Tag)
    (attack : Program Input Tag (Input × Tag)) (epsilon : ℝ≥0∞)
    (prf : eventProb (familyExperiment keys evaluate (checkedAttack [] attack)) (· = true) ≤
      eventProb (idealExperiment (checkedAttack [] attack)) (· = true) + epsilon) :
    eventProb (keyedGame keys evaluate attack) (· = true) ≤
      epsilon + (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ eventProb (game attack) (· = true) + epsilon := prf
    _ ≤ (Fintype.card Tag : ℝ≥0∞)⁻¹ + epsilon := add_le_add (secure attack) le_rfl
    _ = _ := add_comm _ _

/-- The local state transformations used in the certificate. The reserve
function is secret; the applied-set register is also hidden from the attack. -/
def presentation (n : Nat) (Tag : Type) : Presentation n where
  State := Finset (Fin n) × (Fin n → Tag)
  vertex := Prod.fst
  step i state := (insert i state.1, state.2)

def localCertificate (n : Nat) (Tag : Type) : LocalCertificate (presentation n Tag) where
  prove slot := by
    rcases slot with i | (i | ⟨i, j⟩)
    · intro state; rfl
    · intro state present
      exact Prod.ext (Finset.insert_eq_of_mem present) rfl
    · intro state _ _ _
      exact Prod.ext (Finset.insert_comm j i state.1) rfl

theorem certificate_cube (n : Nat) (Tag : Type) :
    (localCertificate n Tag).toCube = Cube.cube (Fin n) Tag := rfl

/-- A single supported order is provided as data. Its evaluator takes n
exposure steps, and does not enumerate the n! other orders. -/
noncomputable def scheduledGame {n : Nat} (attack : Program (Fin n) Tag (Fin n × Tag))
    (schedule : Schedule n) : PMF Bool :=
  (uniform (Fin n → Tag)).bind fun key =>
    ((checkedAttack [] attack).run Cube.coordinateOracle
      ((localCertificate n Tag).toCube.run (order schedule) (∅, key))).map Outcome.result

omit [DecidableEq Tag] [Fintype Tag] [Nonempty Tag] in
/-- All orders construct exactly the same retained state, before probability
or an adversary is involved. Its comparison is generated by local squares. -/
theorem scheduled_state {n : Nat} (schedule : Schedule n) (key : Fin n → Tag) :
    (localCertificate n Tag).toCube.run (order schedule) (∅, key) =
      (Cube.cube (Fin n) Tag).query (∅, key) (Finset.univ : Finset (Fin n)) := by
  rw [(localCertificate n Tag).all_orders schedule]
  change (Cube.cube (Fin n) Tag).run (List.finRange n) (∅, key) = _
  rw [StateCube.run_eq_query]
  congr 1
  ext i
  simp

/-- Exact public game equality, for every schedule and every adaptive attack.
The canonical lazy-sampling argument is applied once, after local reconstruction. -/
theorem scheduled_game {n : Nat} (attack : Program (Fin n) Tag (Fin n × Tag))
    (schedule : Schedule n) : scheduledGame attack schedule = game attack := by
  unfold scheduledGame
  simp_rw [scheduled_state, Cube.query_eq, Finset.empty_union]
  have projected := congrArg (PMF.map Prod.fst)
    (Cube.public_correct (checkedAttack [] attack) (Finset.univ : Finset (Fin n)))
  simp only [Cube.publicLaw, PMF.map_bind, PMF.map_comp, Function.comp_def] at projected
  rw [projected, checked_lazy, game_lazy]

/-- The security assertion as a predicate on a retained-state transformer.
This permits the generic shared-certificate checker to transport the entire
game, rather than storing one security proof for each schedule. -/
def securityGoal {n : Nat} (attack : Program (Fin n) Tag (Fin n × Tag))
    (transform : (presentation n Tag).State → (presentation n Tag).State) : Prop :=
  eventProb ((uniform (Fin n → Tag)).bind fun key =>
    ((checkedAttack [] attack).run Cube.coordinateOracle (transform (∅, key))).map
      Outcome.result) (· = true) ≤ (Fintype.card Tag : ℝ≥0∞)⁻¹

/-- The actual shared certificate has local laws and only the canonical
security argument. It contains no schedule-indexed family of security proofs. -/
def securityCertificate {n : Nat} (attack : Program (Fin n) Tag (Fin n × Tag)) :
    SharedCertificate (presentation n Tag) (securityGoal attack) where
  laws := localCertificate n Tag
  canonical := by
    change eventProb (scheduledGame attack (Equiv.refl (Fin n))) (· = true) ≤ _
    rw [scheduled_game]
    exact secure attack

theorem all_schedules_secure {n : Nat} (attack : Program (Fin n) Tag (Fin n × Tag)) :
    ∀ schedule : Schedule n,
      eventProb (scheduledGame attack schedule) (· = true) ≤
        (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  intro schedule
  exact (securityCertificate attack).sound schedule

omit [DecidableEq Tag] [Fintype Tag] [Nonempty Tag] in
theorem exposure_steps {n : Nat} (schedule : Schedule n) (key : Fin n → Tag) :
    ((localCertificate n Tag).toCube.runCount (order schedule) (∅, key)).2 = n := by
  rw [StateCube.runCount_eq, order_length]

/-- The same extracted PRF distinguisher works for every presentation order
of the ideal game. Its distinguishing bound is not multiplied by n!. -/
theorem keyed_all_schedules {n : Nat} {Key : Type} (keys : PMF Key)
    (evaluate : Key → Fin n → Tag) (attack : Program (Fin n) Tag (Fin n × Tag))
    (epsilon : ℝ≥0∞)
    (prf : eventProb (familyExperiment keys evaluate (checkedAttack [] attack)) (· = true) ≤
      eventProb (idealExperiment (checkedAttack [] attack)) (· = true) + epsilon) :
    ∀ schedule : Schedule n,
      eventProb (keyedGame keys evaluate attack) (· = true) ≤
        eventProb (scheduledGame attack schedule) (· = true) + epsilon ∧
      eventProb (scheduledGame attack schedule) (· = true) ≤
        (Fintype.card Tag : ℝ≥0∞)⁻¹ := by
  intro schedule
  rw [scheduled_game]
  exact ⟨prf, secure attack⟩

/-- Any literal certificate for exactly the same all-schedules security claim
has factorially many path nodes, while the supplied local slots plus one
canonical security slot have quadratic size. The proof payloads are shared. -/
theorem security_certificate_separation {n : Nat} (large : 3 ≤ n)
    (attack : Program (Fin n) Tag (Fin n × Tag))
    (explicit : ExplicitCertificate n (fun schedule =>
      eventProb (scheduledGame attack schedule) (· = true) ≤
        (Fintype.card Tag : ℝ≥0∞)⁻¹)) :
    sharedSize n = (n + 1) ^ 2 ∧
      (n + 1) * n.factorial ≤ explicit.size ∧ sharedSize n < explicit.size :=
  ⟨shared_size n, explicit.size_lower_bound, smaller_than_enumeration large explicit⟩

end Foundation.Symmetric.RandomFunctionMACSchedules
