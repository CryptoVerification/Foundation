import Foundation.Constructions.Hash.LatentPublication

/-! Recognition across the complete real table and the simulator's public
view. Existing exposed-path invariants are reused. Their preservation in the
joint coordinate experiment is not assumed to follow from a marginal law. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label]
  [Fintype Digest] [Nonempty Digest]

local instance recognitionCompressionBEq : BEq (CompressionInput Payload Digest) := instBEqOfDecidableEq

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- Decoding the symbolic graph gives genuine real data paths. -/
theorem LatentDataRelation.chain_to_real {function : Label → Digest}
    {full : CompressionTable Payload Digest} {state : LatentState Payload Digest Label}
    (relation : LatentDataRelation function full state) {initial target : Digest} {message : List Payload}
    (chain : DataChain initial (latentDecodedGraph function state) message target) :
    DataChain initial full message target := chain.mono relation.sound

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
/-- Terminal rows in the real table add no data paths: every real data chain
is represented in the decoded symbolic graph by the relation's completeness. -/
theorem LatentDataRelation.chain_from_real {function : Label → Digest}
    {full : CompressionTable Payload Digest} {state : LatentState Payload Digest Label}
    (relation : LatentDataRelation function full state) {initial target : Digest} {message : List Payload}
    (chain : DataChain initial full message target) :
    DataChain initial (latentDecodedGraph function state) message target := by
  induction chain with
  | nil => exact .nil
  | snoc block chain edge ih => exact .snoc block ih (relation.complete _ edge rfl)

omit [Fintype Digest] [Nonempty Digest] in
/-- Absence of the ideal hidden-coordinate guess excludes the corresponding
real hidden-data endpoint at this related state. No probability transfer is
claimed before preservation of the joint relation is established. -/
theorem LatentDataRelation.visible {function : Label → Digest}
    {real : TrackedRealState Payload Digest} {state : LatentState Payload Digest Label}
    (relation : LatentDataRelation function real.full state) (publicSame : real.exposed = state.exposed)
    (value : Digest) (noGuess : ∀ label, state.revealed.lookup label = none → function label ≠ value) :
    value ∉ hiddenDataOutputs real := by
  intro hidden
  obtain ⟨label, pending, same⟩ := relation.hidden_coordinate publicSame value hidden
  exact noGuess label pending same

omit [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
/-- Complete-table and public-table backward searches agree at a visible
endpoint, under the existing reconstructibility and full graph conditions.
Fuel is each table's actual length; equal table lengths are not required. -/
theorem messagePrefix_eq_of_reconstructible (initial : Digest) (real : TrackedRealState Payload Digest)
    (publicSubset : real.exposed ⊆ real.full) (injective : OutputInjective real.full)
    (avoid : AvoidInitial initial real.full) (reconstructible : PublicReconstructible initial real)
    (target : Digest) (visible : target ∉ hiddenDataOutputs real) :
    messagePrefix initial real.full real.full.length target =
      messagePrefix initial real.exposed real.exposed.length target := by
  cases fullSearch : messagePrefix initial real.full real.full.length target with
  | some message =>
      have chain := (messagePrefix_sound initial real.full real.full.length target message fullSearch).1
      exact (reconstructible message target chain visible).symm
  | none =>
      cases publicSearch : messagePrefix initial real.exposed real.exposed.length target with
      | none => rfl
      | some message =>
          have chain := (messagePrefix_sound initial real.exposed real.exposed.length target message publicSearch).1
          have found := messagePrefix_complete injective avoid (chain.mono publicSubset)
          rw [fullSearch] at found
          cases found

omit [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
/-- The executable terminal recognizers agree whenever the existing full/public
path invariant makes the queried endpoint publicly reconstructible. -/
theorem terminalMessage_eq_of_reconstructible (initial : Digest) (terminal : Payload)
    (real : TrackedRealState Payload Digest) (publicSubset : real.exposed ⊆ real.full)
    (injective : OutputInjective real.full) (avoid : AvoidInitial initial real.full)
    (reconstructible : PublicReconstructible initial real) (input : CompressionInput Payload Digest)
    (visible : input.1 ∉ hiddenDataOutputs real) :
    terminalMessage initial terminal real.full input = terminalMessage initial terminal real.exposed input := by
  unfold terminalMessage
  rw [messagePrefix_eq_of_reconstructible initial real publicSubset injective avoid reconstructible input.1 visible]

omit [Fintype Digest] [Nonempty Digest] in
/-- Concrete real/ideal recognizer agreement. Forward freshness and exposed
paths are the existing real invariants, not a false chronological freshness
claim about the simulator's public table. Their preservation in a coupled
execution is still needed for the final indifferentiability theorem. -/
theorem LatentDataRelation.terminal_recognition {function : Label → Digest}
    {real : TrackedRealState Payload Digest} {state : LatentState Payload Digest Label}
    (relation : LatentDataRelation function real.full state) (publicSame : real.exposed = state.exposed)
    (initial : Digest) (terminal : Payload) (good : ForwardFresh initial real.full)
    (publicConsistent : PublicConsistent real) (paths : ExposedPaths initial real)
    (input : CompressionInput Payload Digest)
    (noGuess : ∀ label, state.revealed.lookup label = none → function label ≠ input.1) :
    terminalMessage initial terminal real.full input = terminalMessage initial terminal state.exposed input := by
  obtain ⟨injective, avoid⟩ := freshOutputs_graph good.outputs
  have subset := publicConsistent.public_subset
  have publicInjective : OutputInjective real.exposed := by
    intro left hl right hr equal
    exact injective left (subset hl) right (subset hr) equal
  have publicAvoid : AvoidInitial initial real.exposed := fun entry member => avoid entry (subset member)
  have reconstructible : PublicReconstructible initial real := by
    intro message target chain visible
    exact messagePrefix_complete publicInjective publicAvoid (paths.not_hidden chain visible)
  have recognized := terminalMessage_eq_of_reconstructible initial terminal real subset injective avoid
    reconstructible input (relation.visible publicSame input.1 noGuess)
  rwa [publicSame] at recognized

/-- Every actual compression result produced by the existing simulator
procedure is a supported ideal-compression result after forgetting backend
state. This holds for any backend, and asserts no probability equality. -/
theorem simulator_step_support {BackendState : Type}
    (backend : Oracle (SimulatorRequest Payload) Digest BackendState)
    (initial : Digest) (terminal : Payload) (full : CompressionTable Payload Digest)
    (state : BackendState) (input : CompressionInput Payload Digest)
    (answer : (CompressionTable Payload Digest × BackendState) × Digest)
    (support : answer ∈ (Program.statefulOracle (simulatorProgram initial terminal) backend
      (full, state) input).support) :
    (answer.1.1, answer.2) ∈ (RandomOracle.oracle full input).support := by
  unfold Program.statefulOracle at support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨out, reachable, rfl⟩ := support
  cases cached : full.lookup input with
  | some output =>
      have real := RandomOracle.known full input output cached
      simp only [List.lookup_eq_findSome?, beq_iff_eq] at cached
      simp only [simulatorProgram, List.lookup_eq_findSome?, beq_iff_eq, cached,
        Program.run, PMF.mem_support_pure_iff] at reachable
      subst out
      rw [real]
      simp
  | none =>
      have real := RandomOracle.fresh full input cached
      simp only [List.lookup_eq_findSome?, beq_iff_eq] at cached
      simp only [simulatorProgram, List.lookup_eq_findSome?, beq_iff_eq, cached] at reachable
      cases recognized : terminalMessage initial terminal full input <;>
        simp only [recognized, Program.run, PMF.mem_support_bind_iff] at reachable <;>
        obtain ⟨response, _, tailSupport⟩ := reachable <;>
        rw [PMF.mem_support_map_iff] at tailSupport <;>
        obtain ⟨tail, tailSupport, rfl⟩ := tailSupport <;>
        simp only [PMF.mem_support_pure_iff] at tailSupport <;>
        subst tail <;>
        rw [real, PMF.mem_support_map_iff] <;>
        exact ⟨response.2, PMF.mem_support_uniformOfFintype response.2, rfl⟩

/-- Entire adaptive compression programs preserve real reachability, including
all compression queries and results, for an arbitrary simulator backend. -/
theorem simulator_run_support {BackendState Result : Type}
    (backend : Oracle (SimulatorRequest Payload) Digest BackendState)
    (initial : Digest) (terminal : Payload) (full : CompressionTable Payload Digest)
    (state : BackendState) (program : Program (CompressionInput Payload Digest) Digest Result)
    (out : Outcome (CompressionInput Payload Digest) Digest Result (CompressionTable Payload Digest × BackendState))
    (support : out ∈ (program.run
      (Program.statefulOracle (simulatorProgram initial terminal) backend) (full, state)).support) :
    Program.mapState Prod.fst out ∈ (program.run RandomOracle.oracle full).support := by
  exact Program.run_support_state_map Prod.fst _ _
    (fun pair input answer reachable => simulator_step_support backend initial terminal pair.1 pair.2 input answer reachable)
    program (full, state) out support

omit [DecidableEq Label] in
/-- At the original two-window interface, each supported coordinate-real
transition projects to a supported original real transition. No capacity or
coordinate-independence premise is needed for support inclusion. -/
theorem coordinate_real_step_support
    (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    {hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)}
    (state : CoordinateRealState Payload Digest Label) (request : WorldInput Payload Digest)
    (answer : CoordinateRealState Payload Digest Label × Digest)
    (support : answer ∈ (coordinateRealWorld initial terminal coordinates hashOracle state request).support) :
    (answer.1.1, answer.2) ∈ (realWorld initial terminal state.1 request).support := by
  have world : Program.implementedOracle (compressionCall initial terminal) RandomOracle.oracle =
      realWorld initial terminal := by
    funext table request
    cases request with
    | inl message => rfl
    | inr input =>
        simp [Program.implementedOracle, compressionCall, Program.run, Program.resultState,
          realWorld, PMF.map_bind, PMF.pure_map]
  unfold coordinateRealWorld Program.implementedOracle at support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨out, reachable, rfl⟩ := support
  have projected := simulator_run_support (realCoordinateWorld coordinates hashOracle) initial terminal state.1 state.2
    (compressionCall initial terminal request) out reachable
  rw [← world]
  unfold Program.implementedOracle
  rw [PMF.mem_support_map_iff]
  exact ⟨Program.mapState Prod.fst out, projected, rfl⟩

omit [DecidableEq Label] in
/-- An arbitrary adaptive attack against the coordinate-real world retains a
supported original real outcome with the exact outer public transcript. This
can transfer deterministic real invariants, but not probability bounds. -/
theorem coordinate_real_run_support {Result : Type}
    (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    {hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)}
    (state : CoordinateRealState Payload Digest Label)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (out : Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label))
    (support : out ∈ (attack.run (coordinateRealWorld initial terminal coordinates hashOracle) state).support) :
    Program.mapState Prod.fst out ∈ (attack.run (realWorld initial terminal) state.1).support := by
  exact Program.run_support_state_map Prod.fst _ _
    (coordinate_real_step_support initial terminal coordinates) attack state out support

omit [DecidableEq Label] in
/-- Each coordinate-real outcome from an empty compression table has an
actual original tracked-real witness with the same final full table, result,
and entire public transcript. No claim is made that hidden-guess flags vanish. -/
theorem coordinate_real_tracked_witness {Result : Type}
    (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    {hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)}
    (backend : RealCoordinateState Payload Digest Label)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (out : Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label))
    (support : out ∈ (attack.run (coordinateRealWorld initial terminal coordinates hashOracle) ([], backend)).support) :
    ∃ tracked : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest),
      tracked ∈ (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty).support ∧
      Program.mapState TrackedRealState.full tracked = Program.mapState Prod.fst out := by
  have reachable := coordinate_real_run_support initial terminal coordinates ([], backend) attack out support
  change Program.mapState Prod.fst out ∈
    (attack.run (realWorld initial terminal) TrackedRealState.empty.full).support at reachable
  rw [← trackedReal_run initial terminal attack TrackedRealState.empty, PMF.mem_support_map_iff] at reachable
  exact reachable

/-- The actual ideal-side guess test controls the original real flag at a
related pre-state. Together with the existing real path-preservation theorem,
this transports public-path metadata across the next supported real step. -/
theorem LatentDataRelation.tracked_step_paths [Fintype Label]
    {function : Label → Digest} {real : TrackedRealState Payload Digest}
    {state : LatentState Payload Digest Label}
    (relation : LatentDataRelation function real.full state)
    (initial : Digest) (terminal : Payload) (publicSame : real.exposed = state.exposed)
    (publicConsistent : PublicConsistent real) (paths : ExposedPaths initial real)
    (notGuessed : real.guessed = false)
    (backend : RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest)
    (request : WorldInput Payload Digest) (noHit : latentGuessHit function (state, backend) request = false)
    (answer : TrackedRealState Payload Digest × Digest)
    (support : answer ∈ (trackedRealWorld initial terminal real request).support)
    (good : ForwardFresh initial answer.1.full) :
    answer.1.guessed = false ∧ ExposedPaths initial answer.1 := by
  have notGuessedAfter := trackedReal_step_visible initial terminal real notGuessed request
    (by intro input same hidden
        subst request
        have hit := relation.hidden_guess publicSame backend input hidden
        rw [noHit] at hit
        cases hit) answer support
  exact ⟨notGuessedAfter,
    trackedReal_step_paths initial terminal real publicConsistent paths request answer support good notGuessedAfter⟩

end Foundation.Hash


