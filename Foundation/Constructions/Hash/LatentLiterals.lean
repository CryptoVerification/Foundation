import Foundation.Constructions.Hash.LatentPublication

/-! Literal parents cannot become aliases of coordinates after publication.
The conservative hidden-guess test includes unused labels, so excluding a guess
when a literal parent is introduced separates it from all future coordinates.
These deterministic lemmas still require their exclusions explicitly. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false
variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label]
  [Fintype Digest] [Nonempty Digest]

local instance literalCompressionBEq : BEq (CompressionInput Payload Digest) := instBEqOfDecidableEq
local instance literalGraphBEq : BEq ((Digest ⊕ Label) × Payload) := instBEqOfDecidableEq
local instance literalLabelBEq : BEq Label := instBEqOfDecidableEq

/-- Every literal parent in the actual symbolic graph differs from every
coordinate value, including those not yet allocated or revealed. -/
def LatentState.LiteralAvoids (function : Label → Digest) (state : LatentState Payload Digest Label) : Prop :=
  ∀ edge ∈ state.graph, ∀ literal, edge.1.1 = .inl literal → ∀ label, function label ≠ literal

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem latent_empty_literal_avoids (function : Label → Digest) (supply : List Label) :
    (LatentState.empty (Payload := Payload) supply).LiteralAvoids function := by
  intro edge member
  cases member

omit [DecidableEq Payload] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
/-- Existing literal separation implies the executable inverse-parent choice
remains literal, without a chronological freshness assumption on public rows. -/
theorem LatentState.LiteralAvoids.stable {function : Label → Digest} {state : LatentState Payload Digest Label}
    (separate : state.LiteralAvoids function) (initial : Digest)
    (values : RandomOracle.TableValues function state.revealed) :
    ∀ edge ∈ state.graph, ∀ literal, edge.1.1 = .inl literal →
      latentParent initial state literal = .inl literal := by
  intro edge member literal parent
  have value := latentParent_value initial function state values literal
  cases chosen : latentParent initial state literal with
  | inl output =>
      have same : output = literal := by simpa only [chosen, latentValue, Sum.elim_inl, id_eq] using value
      exact congrArg Sum.inl same
  | inr label =>
      have same : function label = literal := by simpa only [chosen, latentValue, Sum.elim_inr] using value
      exact False.elim (separate edge member literal parent label same)

omit [DecidableEq Payload] [Fintype Digest] [Nonempty Digest] in
/-- A literal chosen at this public query is separated from all coordinates.
Already revealed coordinates are excluded by the actual inverse lookup; every
remaining coordinate is excluded by the current hidden-guess condition. -/
theorem latentParent_literal_avoids (initial : Digest) (function : Label → Digest)
    (injective : Function.Injective function) (state : LatentState Payload Digest Label)
    (values : RandomOracle.TableValues function state.revealed) (avoid : ∀ label, function label ≠ initial)
    (value literal : Digest) (parent : latentParent initial state value = .inl literal)
    (noGuess : ∀ label, state.revealed.lookup label = none → function label ≠ value) :
    ∀ label, function label ≠ literal := by
  have same : literal = value := by
    simpa only [parent, latentValue, Sum.elim_inl, id_eq] using latentParent_value initial function state values value
  subst literal
  intro label equal
  cases known : state.revealed.lookup label with
  | none => exact noGuess label known equal
  | some output =>
      have stored : output = function label := values.lookup known
      have published := latentParent_revealed initial function injective state values label (avoid label)
        (by simpa only [stored] using known)
      rw [equal, parent] at published
      cases published

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem reserveLabel_literal_avoids (function : Label → Digest) (state : LatentState Payload Digest Label)
    (separate : state.LiteralAvoids function) : (reserveLabel state).1.LiteralAvoids function := by
  cases supply : state.supply <;> simpa only [reserveLabel, supply, LatentState.LiteralAvoids] using separate

omit [Fintype Digest] [Nonempty Digest] in
/-- Adding a fresh data edge is safe when its particular symbolic parent is
separated. Known edges and an exhausted allocator do not add literal parents. -/
theorem latentAdvance_literal_avoids (initial : Digest) (function : Label → Digest)
    (state : LatentState Payload Digest Label) (separate : state.LiteralAvoids function)
    (parent : Digest ⊕ Label) (block : Payload)
    (parentSafe : ∀ literal, parent = .inl literal → ∀ label, function label ≠ literal) :
    (latentAdvance initial state parent block).1.LiteralAvoids function := by
  unfold latentAdvance
  split
  · exact separate
  · dsimp only
    cases supply : state.supply with
    | nil => simpa only [reserveLabel, supply, LatentState.LiteralAvoids] using separate
    | cons child rest =>
        simp only [reserveLabel, supply]
        intro edge member literal selected label
        rcases List.mem_cons.mp member with rfl | old
        · exact parentSafe literal selected label
        · exact separate edge old literal selected label

omit [Fintype Digest] [Nonempty Digest] in
/-- The next symbolic data parent is either a label or the fixed initial value,
including the explicitly recorded exhaustion branch. -/
theorem latentAdvance_parent_safe (initial : Digest) (function : Label → Digest)
    (avoid : ∀ label, function label ≠ initial) (state : LatentState Payload Digest Label)
    (parent : Digest ⊕ Label) (block : Payload) :
    ∀ literal, (latentAdvance initial state parent block).2 = .inl literal →
      ∀ label, function label ≠ literal := by
  unfold latentAdvance
  split
  · intro literal impossible; cases impossible
  · dsimp only
    cases supply : state.supply with
    | nil =>
        simp only [reserveLabel, supply]
        intro literal same
        cases same
        exact avoid
    | cons child rest =>
        simp only [reserveLabel, supply]
        intro literal impossible
        cases impossible

omit [Fintype Digest] [Nonempty Digest] in
theorem reserveMessage_literal_avoids (initial : Digest) (function : Label → Digest)
    (avoid : ∀ label, function label ≠ initial) (state : LatentState Payload Digest Label)
    (separate : state.LiteralAvoids function) (parent : Digest ⊕ Label) (message : List Payload)
    (parentSafe : ∀ literal, parent = .inl literal → ∀ label, function label ≠ literal) :
    (reserveMessage initial state parent message).LiteralAvoids function := by
  induction message generalizing state parent with
  | nil => exact separate
  | cons block rest ih =>
      exact ih _ (latentAdvance_literal_avoids initial function state separate parent block parentSafe)
        _ (latentAdvance_parent_safe initial function avoid state parent block)

omit [Fintype Digest] [Nonempty Digest] in
/-- A public fresh edge obeys literal separation under the actual current
no-guess condition. All other branches reuse the existing graph. -/
theorem chooseLatent_literal_avoids (initial : Digest) (function : Label → Digest)
    (injective : Function.Injective function) (state : LatentState Payload Digest Label)
    (values : RandomOracle.TableValues function state.revealed) (avoid : ∀ label, function label ≠ initial)
    (separate : state.LiteralAvoids function) (input : CompressionInput Payload Digest)
    (noGuess : ∀ label, state.revealed.lookup label = none → function label ≠ input.1) :
    (chooseLatent initial state input).1.LiteralAvoids function := by
  unfold chooseLatent
  split
  · dsimp only
    split
    · split
      · exact separate
      · exact reserveLabel_literal_avoids function state separate
    · cases supply : state.supply with
      | nil => simpa only [reserveLabel, supply, LatentState.LiteralAvoids] using separate
      | cons child rest =>
          simp only [reserveLabel, supply]
          intro edge member literal selected label
          rcases List.mem_cons.mp member with rfl | old
          · exact latentParent_literal_avoids initial function injective state values avoid input.1 literal selected noGuess label
          · exact separate edge old literal selected label
  · exact reserveLabel_literal_avoids function state separate

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
theorem finishLatent_literal_avoids (function : Label → Digest) (state : LatentState Payload Digest Label)
    (separate : state.LiteralAvoids function) (input : CompressionInput Payload Digest)
    (selected : Option Label) (output : Digest) : (finishLatent state input selected output).LiteralAvoids function := by
  cases selected <;> exact separate

omit [Fintype Digest] [Nonempty Digest] in
/-- The actual symbolic procedure preserves literal separation for every
backend response. A high call only introduces the initial literal; a public
call uses its current no-guess condition. This is not a new abstract game. -/
theorem latentProgram_literal_avoids {Backend : Type} (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (injective : Function.Injective function)
    (avoid : ∀ label, function label ≠ initial) (state : LatentState Payload Digest Label)
    (values : RandomOracle.TableValues function state.revealed) (separate : state.LiteralAvoids function)
    (request : WorldInput Payload Digest)
    (noGuess : ∀ input, request = .inr input → ∀ label,
      state.revealed.lookup label = none → function label ≠ input.1)
    (backend : Oracle (LatentRequest Payload Label) Digest Backend) (backendState : Backend)
    (out : Outcome (LatentRequest Payload Label) Digest (LatentState Payload Digest Label × Digest) Backend)
    (support : out ∈ ((latentProgram initial terminal state request).run backend backendState).support) :
    out.result.1.LiteralAvoids function := by
  have querySafe (query : LatentRequest Payload Label) (next : Digest → LatentState Payload Digest Label)
      (safe : ∀ output, (next output).LiteralAvoids function)
      (out : Outcome (LatentRequest Payload Label) Digest (LatentState Payload Digest Label × Digest) Backend)
      (support : out ∈ ((Program.query query (fun output => Program.done (next output, output))).run
        backend backendState).support) : out.result.1.LiteralAvoids function := by
    rw [Program.run, PMF.mem_support_bind_iff] at support
    obtain ⟨answer, _, support⟩ := support
    rw [PMF.mem_support_map_iff] at support
    obtain ⟨tail, reachable, rfl⟩ := support
    simp only [Program.run, PMF.mem_support_pure_iff] at reachable
    subst tail
    exact safe answer.2
  cases request with
  | inl message =>
      apply querySafe (.inl message) (fun _ => reserveMessage initial state (.inl initial) message) _ out support
      intro output
      exact reserveMessage_literal_avoids initial function avoid state separate (.inl initial) message
        (by intro literal same; cases same; exact avoid)
  | inr input =>
      cases cached : state.exposed.lookup input with
      | some output =>
          simp only [latentProgram, cached, Program.run, PMF.mem_support_pure_iff] at support
          subst out
          exact separate
      | none =>
          cases recognized : terminalMessage initial terminal state.exposed input with
          | some message =>
              simp only [latentProgram, cached, recognized] at support
              exact querySafe (.inl message) (fun output => {state with exposed := (input, output) :: state.exposed})
                (fun _ => separate) out support
          | none =>
              simp only [latentProgram, cached, recognized] at support
              exact querySafe (.inr (chooseLatent initial state input).2)
                (fun output => finishLatent (chooseLatent initial state input).1 input
                  (chooseLatent initial state input).2 output)
                (fun output => finishLatent_literal_avoids function _
                  (chooseLatent_literal_avoids initial function injective state values avoid separate input
                    (noGuess input rfl)) input _ output) out support

/-- Lift the procedure proof to the actual outer coordinate world, with
arbitrary independent coordinate and hash kernels. Values and exclusions are
conditions on the starting state, not implicit distributional assumptions. -/
theorem latent_coordinate_step_literal_avoids (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (injective : Function.Injective function)
    (avoid : ∀ label, function label ≠ initial) (state : LatentWorldState Payload Digest Label)
    (values : RandomOracle.TableValues function state.1.revealed) (separate : state.1.LiteralAvoids function)
    (request : WorldInput Payload Digest)
    (noGuess : ∀ input, request = .inr input → ∀ label,
      state.1.revealed.lookup label = none → function label ≠ input.1)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (answer : LatentWorldState Payload Digest Label × Digest)
    (support : answer ∈ (latentCoordinateWorld initial terminal coordinates hashOracle state request).support) :
    answer.1.1.LiteralAvoids function := by
  unfold latentCoordinateWorld Program.statefulOracle at support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨out, reachable, same⟩ := support
  have safe := latentProgram_literal_avoids initial terminal function injective avoid state.1 values separate request
    noGuess _ state.2 out reachable
  have controls : out.result.1 = answer.1.1 := congrArg (fun result => result.1.1) same
  rwa [controls] at safe

omit [DecidableEq Payload] [Fintype Digest] [Nonempty Digest] in
/-- The existing current-query monitor test excludes every unrevealed label,
including unused supply labels. This connects the probability event to the
concrete exclusion used when introducing a literal graph parent. -/
theorem latentGuessHit_no_guess [Fintype Label] (function : Label → Digest)
    (state : LatentWorldState Payload Digest Label) (input : CompressionInput Payload Digest)
    (miss : latentGuessHit function state (.inr input) = false) :
    ∀ label, state.1.revealed.lookup label = none → function label ≠ input.1 := by
  have absent : ¬∃ label ∈ unrevealedLabels state.1,
      function label ∈ nextLowGuesses (some (.inr input)) := of_decide_eq_false miss
  intro label hidden equal
  apply absent
  refine ⟨label, ?_, ?_⟩
  · apply List.mem_filter.mpr
    exact ⟨Finset.mem_toList.mpr (Finset.mem_univ label), by simp only [hidden, decide_true]⟩
  · simp only [nextLowGuesses, List.mem_singleton, equal]

/-- All actual adaptive executions retain coherence and fixed-coordinate
values. If the historical guess flag remains false, literal separation is
preserved throughout the interaction as well. The exclusions on the function
are explicit; the hash kernel can be any independent kernel. -/
theorem latent_monitored_run_invariants [Fintype Label] {Result : Type}
    (initial : Digest) (terminal : Payload) (supply : List Label) (function : Label → Digest)
    (injective : Function.Injective function) (avoid : ∀ label, function label ≠ initial)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label × Bool))
    (support : out ∈ (attack.run (Program.monitorOracle (latentGuessHit function)
      (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle))
      ((LatentState.empty supply, ([], [])), false)).support) :
    LatentCoherent out.state.1 ∧ RandomOracle.TableValues function out.state.1.1.revealed ∧
      (out.state.2 = false → out.state.1.1.LiteralAvoids function) := by
  apply Program.run_preserves
    (Program.monitorOracle (latentGuessHit function)
      (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle))
    (fun state => LatentCoherent state.1 ∧ RandomOracle.TableValues function state.1.1.revealed ∧
      (state.2 = false → state.1.1.LiteralAvoids function)) _ attack
    ((LatentState.empty supply, ([], [])), false) _ out support
  · intro before valid request after reachable
    rw [Program.monitorOracle, PMF.mem_support_map_iff] at reachable
    obtain ⟨answer, reachable, rfl⟩ := reachable
    refine ⟨latent_coordinate_eager_step_coherent initial terminal function hashOracle before.1 valid.1 request answer reachable,
      latent_coordinate_eager_step_values initial terminal function hashOracle before.1 valid.1 valid.2.1 request answer reachable, ?_⟩
    intro unmarked
    have previous := (Bool.or_eq_false_iff.mp unmarked).1
    have miss := (Bool.or_eq_false_iff.mp unmarked).2
    apply latent_coordinate_step_literal_avoids initial terminal function injective avoid before.1 valid.2.1
      (valid.2.2 previous) request _ (RandomOracle.eager function) hashOracle answer reachable
    intro input same
    rw [same] at miss
    exact latentGuessHit_no_guess function before.1 input miss
  · exact ⟨latent_empty_coherent supply, (fun _ member => by cases member),
      fun _ => latent_empty_literal_avoids function supply⟩

/-- The previous one-query literal-stability obligation now holds after every
actual monitored interaction that has never guessed an unrevealed coordinate. -/
theorem latent_monitored_run_literal_stable [Fintype Label] {Result : Type}
    (initial : Digest) (terminal : Payload) (supply : List Label) (function : Label → Digest)
    (injective : Function.Injective function) (avoid : ∀ label, function label ≠ initial)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label × Bool))
    (support : out ∈ (attack.run (Program.monitorOracle (latentGuessHit function)
      (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle))
      ((LatentState.empty supply, ([], [])), false)).support)
    (noHit : out.state.2 = false) :
    ∀ edge ∈ out.state.1.1.graph, ∀ literal, edge.1.1 = .inl literal →
      latentParent initial out.state.1.1 literal = .inl literal := by
  have invariant := latent_monitored_run_invariants initial terminal supply function injective avoid hashOracle attack out support
  exact (invariant.2.2 noHit).stable initial invariant.2.1

end Foundation.Hash
