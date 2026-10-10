import Foundation.Constructions.Hash.FactoredReal
import Foundation.Crypto.Semantics.Oracle.FiniteRequests

/-! Finite-coordinate realization of the factored real experiment's local
uniform draws. The controller allocates a new coordinate on each local draw.
Context hash requests are unchanged. Empty supply is an explicit fallback,
which bounded execution proves unreachable at the chosen capacity. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label]
  [Fintype Digest] [Nonempty Digest]

abbrev RealSupply (Label : Type) := List Label × Bool
abbrev RealCoordinateState (Payload Digest Label : Type) := RealSupply Label ×
  (RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest)

/-- The flag records an actual fallback, rather than an assumed bound. -/
def realCoordinateProgram (supply : RealSupply Label) : SimulatorRequest Payload →
    Program (SimulatorRequest Payload ⊕ Label) Digest (RealSupply Label × Digest)
  | .inl message => .query (.inl (.inl message)) (fun output => .done (supply, output))
  | .inr () => match supply.1 with
      | [] => .query (.inl (.inr ())) (fun output => .done (([], true), output))
      | label :: rest => .query (.inr label) (fun output => .done ((rest, supply.2), output))

noncomputable def realCoordinateWorld
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    Oracle (SimulatorRequest Payload) Digest (RealCoordinateState Payload Digest Label) :=
  Program.statefulOracle realCoordinateProgram
    (RandomOracle.withContext (simulatorBackend hashOracle) coordinates)

def RealCoordinateValid (state : RealCoordinateState Payload Digest Label) : Prop :=
  state.1.1.Nodup ∧ ∀ label ∈ state.1.1, state.2.2.lookup label = none

omit [DecidableEq Digest] [DecidableEq Label] in
/-- Derived interpreter equation; the source's local-draw request is replaced
by exactly one coordinate query whenever a supply label is available. -/
theorem realCoordinateWorld_eq
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (state : RealCoordinateState Payload Digest Label) (request : SimulatorRequest Payload)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    realCoordinateWorld coordinates hashOracle state request = match request with
      | .inl message => (hashOracle state.2.1 message).map
          (fun answer => ((state.1, (answer.1, state.2.2)), answer.2))
      | .inr () => match state.1.1 with
          | [] => (uniform Digest).map (fun output => ((([], true), state.2), output))
          | label :: rest => (coordinates state.2.2 label).map
              (fun answer => (((rest, state.1.2), (state.2.1, answer.1)), answer.2)) := by
  rcases state with ⟨⟨supply, flag⟩, hashes, table⟩
  cases request with
  | inl message =>
      simp [realCoordinateWorld, Program.statefulOracle, realCoordinateProgram,
        Program.run, RandomOracle.withContext, simulatorBackend, PMF.map_bind,
        PMF.pure_map, Function.comp_def]
      rfl
  | inr token =>
      cases token
      cases supply <;>
        simp [realCoordinateWorld, Program.statefulOracle, realCoordinateProgram,
          Program.run, RandomOracle.withContext, simulatorBackend, PMF.map_bind,
          PMF.pure_map, PMF.map_comp, Function.comp_def] <;> rfl

omit [DecidableEq Digest] in
/-- Fresh-coordinate realizations have exactly the original local uniform
marginal, including the shared ideal-hash table after a request. -/
theorem realCoordinate_step_project (state : RealCoordinateState Payload Digest Label)
    (valid : RealCoordinateValid state) (request : SimulatorRequest Payload) :
    (realCoordinateWorld RandomOracle.oracle RandomOracle.oracle state request).map
      (fun answer => (answer.1.2.1, answer.2)) = simulatorBackend RandomOracle.oracle state.2.1 request := by
  rw [realCoordinateWorld_eq]
  cases request with
  | inl message =>
      simp only [simulatorBackend, PMF.map_comp]
      change PMF.map id _ = _
      exact PMF.map_id _
  | inr token =>
      cases token
      dsimp only
      cases remaining : state.1.1 with
      | nil => simp only [simulatorBackend, PMF.map_comp]; rfl
      | cons label rest =>
          dsimp only
          have fresh := valid.2 label (by rw [remaining]; exact List.mem_cons_self)
          rw [RandomOracle.fresh state.2.2 label fresh]
          simp only [simulatorBackend, PMF.map_comp]
          rfl

omit [DecidableEq Digest] in
theorem realCoordinate_step_valid
    {hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)}
    (state : RealCoordinateState Payload Digest Label)
    (valid : RealCoordinateValid state) (request : SimulatorRequest Payload)
    (answer : RealCoordinateState Payload Digest Label × Digest)
    (support : answer ∈ (realCoordinateWorld RandomOracle.oracle hashOracle state request).support) :
    RealCoordinateValid answer.1 := by
  rw [realCoordinateWorld_eq RandomOracle.oracle state request hashOracle] at support
  cases request with
  | inl message =>
      rw [PMF.mem_support_map_iff] at support
      obtain ⟨response, _, rfl⟩ := support
      exact valid
  | inr token =>
      cases token
      cases remaining : state.1.1 with
      | nil =>
          simp only [remaining] at support
          rw [PMF.mem_support_map_iff] at support
          obtain ⟨output, _, rfl⟩ := support
          exact ⟨by simp, by simp⟩
      | cons label rest =>
          simp only [remaining] at support
          rw [PMF.mem_support_map_iff] at support
          obtain ⟨response, reachable, rfl⟩ := support
          have fresh := valid.2 label (by rw [remaining]; exact List.mem_cons_self)
          rw [RandomOracle.fresh state.2.2 label fresh, PMF.mem_support_map_iff] at reachable
          obtain ⟨output, _, rfl⟩ := reachable
          have nodup : (label :: rest).Nodup := remaining ▸ valid.1
          refine ⟨nodup.tail, ?_⟩
          intro other member
          have old := valid.2 other (by rw [remaining]; exact List.mem_cons_of_mem _ member)
          have different : other ≠ label := by
            intro equal
            exact (List.nodup_cons.mp nodup).1 (equal ▸ member)
          simpa only [List.lookup_cons, beq_eq_false_iff_ne.mpr different, Bool.false_eq_true,
            ↓reduceIte] using old

omit [DecidableEq Digest] in
/-- Arbitrary adaptive programs retain the original result, hash state and
entire source transcript when coordinate bookkeeping is forgotten. -/
theorem realCoordinate_run_project {Result : Type}
    (program : Program (SimulatorRequest Payload) Digest Result)
    (state : RealCoordinateState Payload Digest Label) (valid : RealCoordinateValid state) :
    (program.run (realCoordinateWorld RandomOracle.oracle) state).map
      (Program.mapState (fun state => state.2.1)) =
      program.run (simulatorBackend RandomOracle.oracle) state.2.1 :=
  Program.run_state_map_of_invariant (fun state => state.2.1) _ _ RealCoordinateValid
    realCoordinate_step_valid realCoordinate_step_project program state valid

def realCoordinateCompiled {Result : Type} (supply : List Label)
    (program : Program (SimulatorRequest Payload) Digest Result) :
    Program (SimulatorRequest Payload ⊕ Label) Digest (RealSupply Label × Result) :=
  Program.inlineState realCoordinateProgram (supply, false) program

omit [DecidableEq Digest] [DecidableEq Label] in
/-- Inlining the allocator uses the same existing stateful compiler as the
latent ideal program. This statement allows eager or lazy coordinate backends. -/
theorem real_coordinate_inline {Result : Type} (supply : List Label)
    (program : Program (SimulatorRequest Payload) Digest Result)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashes : RandomOracle.Table (List Payload) Digest) (table : RandomOracle.Table Label Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    ((realCoordinateCompiled supply program).run
      (RandomOracle.withContext (simulatorBackend hashOracle) coordinates) (hashes, table)).map
        Program.resultState =
      (program.run (realCoordinateWorld coordinates hashOracle) ((supply, false), (hashes, table))).map
        (fun out => (out.state.2, (out.state.1, out.result))) :=
  Program.inlineState_run realCoordinateProgram program
    (RandomOracle.withContext (simulatorBackend hashOracle) coordinates) (supply, false) (hashes, table)

omit [DecidableEq Digest] in
/-- Exact compiled source marginal, with no condition on supply length: empty
supply is explicit independent local randomness, never a reused coordinate. -/
theorem real_coordinate_compiled {Result : Type} (supply : List Label) (nodup : supply.Nodup)
    (program : Program (SimulatorRequest Payload) Digest Result)
    (hashes : RandomOracle.Table (List Payload) Digest) :
    ((realCoordinateCompiled supply program).run
      (RandomOracle.withContext (simulatorBackend RandomOracle.oracle) RandomOracle.oracle) (hashes, [])).map
        (fun out => (out.state.1, out.result.2)) =
      (program.run (simulatorBackend RandomOracle.oracle) hashes).map Program.resultState := by
  have compiled := congrArg (PMF.map (fun pair => (pair.1.1, pair.2.2)))
    (real_coordinate_inline supply program RandomOracle.oracle hashes [])
  have valid : RealCoordinateValid (((supply, false), (hashes, [])) : RealCoordinateState Payload Digest Label) :=
    ⟨nodup, by intro label _; simp⟩
  have erased := congrArg (PMF.map Program.resultState)
    (realCoordinate_run_project program _ valid)
  simp only [PMF.map_comp, Program.resultState, Program.mapState, Function.comp_def] at compiled erased
  exact compiled.trans erased

omit [DecidableEq Digest] in
/-- Integrating one finite coordinate function preserves the entire compiled
outcome, including all hash/coordinate state and its interleaved target trace. -/
theorem real_coordinate_eager [Fintype Label] {Result : Type} (supply : List Label)
    (program : Program (SimulatorRequest Payload) Digest Result)
    (hashes : RandomOracle.Table (List Payload) Digest) :
    (uniform (Label → Digest)).bind (fun function =>
      (realCoordinateCompiled supply program).run
        (RandomOracle.withContext (simulatorBackend RandomOracle.oracle) (RandomOracle.eager function)) (hashes, [])) =
      (realCoordinateCompiled supply program).run
        (RandomOracle.withContext (simulatorBackend RandomOracle.oracle) RandomOracle.oracle) (hashes, []) :=
  RandomOracle.eager_lazy_context (simulatorBackend RandomOracle.oracle) (realCoordinateCompiled supply program) hashes []

/-- The finite-coordinate real experiment has the original real-world marginal.
Both this program and the latent ideal compiled program now use the same target
request alphabet, ideal-hash kernel and finite coordinate function. -/
theorem real_coordinate_real_marginal [Fintype Label] {Result : Type} (supply : List Label) (nodup : supply.Nodup)
    (initial : Digest) (terminal : Payload) (attack : Program (WorldInput Payload Digest) Digest Result) :
    (uniform (Label → Digest)).bind (fun function =>
      ((realCoordinateCompiled supply (factoredRealCompiled initial terminal attack)).run
        (RandomOracle.withContext (simulatorBackend RandomOracle.oracle) (RandomOracle.eager function)) ([], [])).map
          (fun out => out.result.2)) =
      (attack.run (realWorld initial terminal) []).map Program.resultState := by
  rw [← PMF.map_bind, real_coordinate_eager]
  have compiled := congrArg (PMF.map Prod.snd)
    (real_coordinate_compiled supply nodup (factoredRealCompiled initial terminal attack) [])
  simp only [PMF.map_comp, Program.resultState, Function.comp_def] at compiled
  exact compiled.trans (factored_real_compiled initial terminal attack)


omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem realCoordinateProgram_queries (supply : RealSupply Label) (request : SimulatorRequest Payload) :
    (realCoordinateProgram (Digest := Digest) supply request).BoundedQueries 1 := by
  cases request with
  | inl message => exact .query _ _ 0 (fun _ => .done _ 0)
  | inr token =>
      cases token
      cases remaining : supply.1 <;>
        simp only [realCoordinateProgram, remaining] <;> exact .query _ _ 0 (fun _ => .done _ 0)

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem real_coordinate_compiled_queries {Result : Type} (supply : List Label)
    {program : Program (SimulatorRequest Payload) Digest Result} {q : Nat} (bound : program.BoundedQueries q) :
    (realCoordinateCompiled supply program).BoundedQueries q := by
  simpa only [realCoordinateCompiled, Nat.mul_one] using
    Program.inlineState_queries realCoordinateProgram 1 realCoordinateProgram_queries bound (supply, false)

omit [DecidableEq Digest] [DecidableEq Label] in
theorem realCoordinate_step_resource
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (state : RealCoordinateState Payload Digest Label) (request : SimulatorRequest Payload)
    (answer : RealCoordinateState Payload Digest Label × Digest)
    (support : answer ∈ (realCoordinateWorld coordinates RandomOracle.oracle state request).support) :
    state.1.1.length ≤ answer.1.1.1.length + 1 ∧
      (1 ≤ state.1.1.length → answer.1.1.2 = state.1.2) := by
  rw [realCoordinateWorld_eq] at support
  cases request with
  | inl message =>
      rw [PMF.mem_support_map_iff] at support
      obtain ⟨response, _, rfl⟩ := support
      exact ⟨by dsimp only; omega, fun _ => rfl⟩
  | inr token =>
      cases token
      cases remaining : state.1.1 with
      | nil =>
          simp only [remaining] at support
          rw [PMF.mem_support_map_iff] at support
          obtain ⟨output, _, rfl⟩ := support
          exact ⟨by simp, by simp⟩
      | cons label rest =>
          simp only [remaining] at support
          rw [PMF.mem_support_map_iff] at support
          obtain ⟨response, _, rfl⟩ := support
          exact ⟨by simp, fun _ => rfl⟩

omit [DecidableEq Digest] [DecidableEq Label] in
/-- A q-call source program consumes at most q coordinates. Sufficient initial
capacity prevents fallback on every supported path, for any coordinate kernel. -/
theorem realCoordinate_run_resource {Result : Type}
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    {program : Program (SimulatorRequest Payload) Digest Result} {q : Nat} (bound : program.BoundedQueries q)
    (state : RealCoordinateState Payload Digest Label)
    (out : Outcome (SimulatorRequest Payload) Digest Result (RealCoordinateState Payload Digest Label))
    (support : out ∈ (program.run (realCoordinateWorld coordinates) state).support) :
    state.1.1.length ≤ out.state.1.1.length + q ∧
      (q ≤ state.1.1.length → out.state.1.2 = state.1.2) := by
  induction bound generalizing state out with
  | done result q =>
      rw [Program.run, PMF.mem_support_pure_iff] at support
      subst out
      exact ⟨by dsimp only; omega, fun _ => rfl⟩
  | coin next q bound ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, reachable⟩ := support
      exact ih bit state out reachable
  | query request next q bound ih =>
      rw [Program.run, PMF.mem_support_bind_iff] at support
      obtain ⟨answer, reachable, rest⟩ := support
      rw [PMF.mem_support_map_iff] at rest
      obtain ⟨tail, tailSupport, rfl⟩ := rest
      have first := realCoordinate_step_resource coordinates state request answer reachable
      have last := ih answer.2 answer.1 tail tailSupport
      refine ⟨by dsimp only; have := first.1; have := last.1; omega, ?_⟩
      intro available
      exact (last.2 (by have := first.1; omega)).trans (first.2 (by omega))

omit [DecidableEq Digest] [DecidableEq Label] in
theorem real_coordinate_compiled_no_fallback {Result : Type} (supply : List Label)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    {program : Program (SimulatorRequest Payload) Digest Result} {q : Nat} (bound : program.BoundedQueries q)
    (available : q ≤ supply.length) (hashes : RandomOracle.Table (List Payload) Digest)
    (table : RandomOracle.Table Label Digest)
    (out : Outcome (SimulatorRequest Payload ⊕ Label) Digest (RealSupply Label × Result)
      (RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest))
    (support : out ∈ ((realCoordinateCompiled supply program).run
      (RandomOracle.withContext (simulatorBackend RandomOracle.oracle) coordinates) (hashes, table)).support) :
    out.result.1.2 = false := by
  have mapped : Program.resultState out ∈ (((realCoordinateCompiled supply program).run
      (RandomOracle.withContext (simulatorBackend RandomOracle.oracle) coordinates) (hashes, table)).map
        Program.resultState).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨out, support, rfl⟩
  rw [real_coordinate_inline, PMF.mem_support_map_iff] at mapped
  obtain ⟨sourceOut, reachable, same⟩ := mapped
  have flag := (realCoordinate_run_resource coordinates bound ((supply, false), (hashes, table)) sourceOut reachable).2 available
  have sameSupply : sourceOut.state.1 = out.result.1 := congrArg (fun pair => pair.2.1) same
  rwa [sameSupply] at flag

/-- The real experiment uses Fin(q*blockLimit), the very same coordinate type
as the ideal experiment's capacity theorem. Fallback is excluded for each fixed
function and each supported execution, not merely with high probability. -/
theorem real_coordinate_fin_capacity {Result : Type} {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) (function : Fin (q * blockLimit) → Digest)
    (out : Outcome (SimulatorRequest Payload ⊕ Fin (q * blockLimit)) Digest
      (RealSupply (Fin (q * blockLimit)) × (CompressionTable Payload Digest × Result))
      (RandomOracle.Table (List Payload) Digest × RandomOracle.Table (Fin (q * blockLimit)) Digest))
    (support : out ∈ ((realCoordinateCompiled (List.finRange (q * blockLimit))
      (factoredRealCompiled initial terminal attack)).run
        (RandomOracle.withContext (simulatorBackend RandomOracle.oracle) (RandomOracle.eager function)) ([], [])).support) :
    out.result.1.2 = false :=
  real_coordinate_compiled_no_fallback (List.finRange (q * blockLimit)) (RandomOracle.eager function)
    (factored_real_compiled_queries bound initial terminal) (by simp) [] [] out support


omit [DecidableEq Digest] [Nonempty Digest] in
/-- Under the certified capacity, even the complete finite set of syntactically
possible requests excludes the local fallback. No probability conditioning is
used to remove that request from the program's domain. -/
theorem real_coordinate_possible_no_fallback {Result : Type} (supply : List Label)
    {program : Program (SimulatorRequest Payload) Digest Result} {q : Nat} (bound : program.BoundedQueries q)
    (available : q ≤ supply.length) :
    (Sum.inl (Sum.inr ()) : SimulatorRequest Payload ⊕ Label) ∉
      (realCoordinateCompiled supply program).possibleRequests := by
  classical
  induction bound generalizing supply with
  | done result q => simp [realCoordinateCompiled, Program.inlineState, Program.possibleRequests]
  | coin next q bound ih =>
      simp only [realCoordinateCompiled, Program.inlineState, Program.possibleRequests, Finset.mem_union, not_or]
      exact ⟨ih false supply available, ih true supply available⟩
  | query request next q bound ih =>
      cases request with
      | inl message =>
          have tails : ∀ response, (Sum.inl (Sum.inr ()) : SimulatorRequest Payload ⊕ Label) ∉
              (realCoordinateCompiled supply (next response)).possibleRequests :=
            fun response => ih response supply (by omega)
          simpa [realCoordinateCompiled, Program.inlineState, realCoordinateProgram, Program.bind,
            Program.possibleRequests] using tails
      | inr token =>
          cases token
          cases remaining : supply with
          | nil => simp [remaining] at available
          | cons label rest =>
              have tails : ∀ response, (Sum.inl (Sum.inr ()) : SimulatorRequest Payload ⊕ Label) ∉
                  (realCoordinateCompiled rest (next response)).possibleRequests :=
                fun response => ih response rest (by simp only [remaining, List.length_cons] at available; omega)
              simpa [realCoordinateCompiled, Program.inlineState, realCoordinateProgram, Program.bind,
                Program.possibleRequests, remaining] using tails

end Foundation.Hash
