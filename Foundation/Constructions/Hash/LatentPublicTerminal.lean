import Foundation.Constructions.Hash.LatentDataLoop

/-! Public cached and terminal calls of the concrete coordinate worlds.
The existing real/public reconstruction invariants justify terminal recognition.
These are actual supported transitions, not assumed response equalities. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label]
  [Fintype Digest] [Nonempty Digest]

local instance publicTerminalCompressionBEq : BEq (CompressionInput Payload Digest) := instBEqOfDecidableEq
local instance publicTerminalGraphBEq : BEq ((Digest ⊕ Label) × Payload) := instBEqOfDecidableEq
local instance publicTerminalLabelBEq : BEq Label := instBEqOfDecidableEq

/-- An actually cached public call makes no backend query in the symbolic
world, for arbitrary coordinate and hash kernels. -/
theorem latent_coordinate_public_known (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : LatentWorldState Payload Digest Label) (input : CompressionInput Payload Digest)
    (output : Digest) (known : state.1.exposed.lookup input = some output) :
    latentCoordinateWorld initial terminal coordinates hashOracle state (.inr input) = PMF.pure (state, output) := by
  simp only [List.lookup_eq_findSome?, beq_iff_eq] at known
  simp [latentCoordinateWorld, Program.statefulOracle, latentProgram, List.lookup_eq_findSome?, beq_iff_eq,
    known, Program.run, PMF.pure_map]

/-- A fresh publicly recognized terminal calls precisely the independent
hash window and records its answer. Coordinate cache and supply are untouched. -/
theorem latent_coordinate_terminal_execution (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : LatentState Payload Digest Label)
    (hashes : RandomOracle.Table (List Payload) Digest) (table : RandomOracle.Table Label Digest)
    (input : CompressionInput Payload Digest) (message : List Payload)
    (fresh : state.exposed.lookup input = none)
    (recognized : terminalMessage initial terminal state.exposed input = some message) :
    latentCoordinateWorld initial terminal coordinates hashOracle (state, (hashes, table)) (.inr input) =
      (hashOracle hashes message).map (fun answer =>
        (({state with exposed := (input, answer.2) :: state.exposed}, (answer.1, table)), answer.2)) := by
  simp only [List.lookup_eq_findSome?, beq_iff_eq] at fresh
  simp [latentCoordinateWorld, Program.statefulOracle, latentProgram, List.lookup_eq_findSome?, beq_iff_eq,
    fresh, recognized, Program.run, Program.adaptOracle, latentContextRequest, RandomOracle.withContext,
    simulatorBackend, PMF.map_bind, PMF.pure_map, PMF.map_comp, Function.comp_def]
  rfl

/-- Public/full consistency makes a cached public answer an actual cached
real compression answer. Both supported transitions leave all states unchanged. -/
theorem coordinate_public_known_pair (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (real : TrackedRealState Payload Digest)
    (state : LatentState Payload Digest Label) (publicSame : real.exposed = state.exposed)
    (publicConsistent : PublicConsistent real) (relation : LatentDataRelation function real.full state)
    (realHashes idealHashes : RandomOracle.Table (List Payload) Digest)
    (realCoordinates idealCoordinates : RandomOracle.Table Label Digest) (flag : Bool)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (input : CompressionInput Payload Digest) (output : Digest)
    (known : state.exposed.lookup input = some output)
    (realAnswer : CoordinateRealState Payload Digest Label × Digest)
    (idealAnswer : LatentWorldState Payload Digest Label × Digest)
    (realSupport : realAnswer ∈ (coordinateRealWorld initial terminal (RandomOracle.eager function) hashOracle
      (real.full, ((state.supply, flag), (realHashes, realCoordinates))) (.inr input)).support)
    (idealSupport : idealAnswer ∈ (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle
      (state, (idealHashes, idealCoordinates)) (.inr input)).support) :
    realAnswer.2 = idealAnswer.2 ∧
    LatentDataRelation function realAnswer.1.1 idealAnswer.1.1 ∧
    realAnswer.1.2.1.1 = idealAnswer.1.1.supply ∧
    realAnswer.1 = (real.full, ((state.supply, flag), (realHashes, realCoordinates))) ∧
    idealAnswer.1 = (state, (idealHashes, idealCoordinates)) := by
  obtain ⟨before, after, table, _⟩ := List.lookup_eq_some_iff.mp known
  have member : (input, output) ∈ real.exposed := by rw [publicSame, table]; simp
  have fullKnown := publicConsistent _ member
  rw [coordinate_real_public_execution, coordinate_real_known initial terminal function real.full
    ((state.supply, flag), (realHashes, realCoordinates)) input output fullKnown hashOracle,
    PMF.mem_support_pure_iff] at realSupport
  subst realAnswer
  rw [latent_coordinate_public_known initial terminal (RandomOracle.eager function) hashOracle
    (state, (idealHashes, idealCoordinates)) input output known, PMF.mem_support_pure_iff] at idealSupport
  subst idealAnswer
  exact ⟨rfl, relation, rfl, rfl, rfl⟩

/-- A publicly recognized terminal agrees in the two actual worlds. A private
cached terminal is covered by the real hash record; a fresh terminal calls the
shared fixed hash function. The two hash caches need not contain the same keys. -/
theorem coordinate_recognized_terminal_pair (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (hashFunction : List Payload → Digest)
    (real : TrackedRealState Payload Digest) (state : LatentState Payload Digest Label)
    (publicSame : real.exposed = state.exposed) (publicConsistent : PublicConsistent real)
    (paths : ExposedPaths initial real) (good : ForwardFresh initial real.full)
    (relation : LatentDataRelation function real.full state)
    (consistent : RandomOracle.TableConsistent real.full)
    (realHashes idealHashes : RandomOracle.Table (List Payload) Digest)
    (realCoordinates idealCoordinates : RandomOracle.Table Label Digest) (flag : Bool)
    (covered : TerminalConsistent initial terminal real.full realHashes)
    (realValues : RandomOracle.TableValues hashFunction realHashes)
    (idealValues : RandomOracle.TableValues hashFunction idealHashes)
    (input : CompressionInput Payload Digest) (message : List Payload)
    (fresh : state.exposed.lookup input = none)
    (recognized : terminalMessage initial terminal state.exposed input = some message)
    (noGuess : ∀ label, state.revealed.lookup label = none → function label ≠ input.1)
    (realAnswer : CoordinateRealState Payload Digest Label × Digest)
    (idealAnswer : LatentWorldState Payload Digest Label × Digest)
    (realSupport : realAnswer ∈ (coordinateRealWorld initial terminal (RandomOracle.eager function)
      (RandomOracle.eager hashFunction) (real.full, ((state.supply, flag), (realHashes, realCoordinates)))
      (.inr input)).support)
    (idealSupport : idealAnswer ∈ (latentCoordinateWorld initial terminal (RandomOracle.eager function)
      (RandomOracle.eager hashFunction) (state, (idealHashes, idealCoordinates)) (.inr input)).support) :
    realAnswer.2 = idealAnswer.2 ∧
    LatentDataRelation function realAnswer.1.1 idealAnswer.1.1 ∧
    realAnswer.1.2.1.1 = idealAnswer.1.1.supply ∧
    RandomOracle.TableConsistent realAnswer.1.1 ∧
    realAnswer.1.2.2.2 = realCoordinates ∧
    RandomOracle.TableValues hashFunction realAnswer.1.2.2.1 ∧
    RandomOracle.TableValues hashFunction idealAnswer.1.2.1 := by
  have fullRecognized : terminalMessage initial terminal real.full input = some message :=
    (relation.terminal_recognition publicSame initial terminal good publicConsistent paths input noGuess).trans recognized
  have sound := terminalMessage_sound initial terminal real.full input message fullRecognized
  rw [latent_coordinate_terminal_execution initial terminal (RandomOracle.eager function)
    (RandomOracle.eager hashFunction) state idealHashes idealCoordinates input message fresh recognized,
    PMF.mem_support_map_iff] at idealSupport
  obtain ⟨idealResponse, idealReachable, rfl⟩ := idealSupport
  have idealStep := RandomOracle.eager_step_values hashFunction idealHashes idealValues message idealResponse idealReachable
  rw [coordinate_real_public_execution] at realSupport
  cases cached : real.full.lookup input with
  | some output =>
      obtain ⟨before, after, table, _⟩ := List.lookup_eq_some_iff.mp cached
      have member : ((input.1, (true, terminal)), output) ∈ real.full := by
        rw [← sound.1, table]; simp
      have registered := covered message input.1 output sound.2 member
      have value := realValues.lookup registered
      rw [coordinate_real_known initial terminal function real.full
        ((state.supply, flag), (realHashes, realCoordinates)) input output cached (RandomOracle.eager hashFunction),
        PMF.mem_support_pure_iff] at realSupport
      subst realAnswer
      have same : output = idealResponse.2 := value.trans idealStep.2.symm
      rw [← same]
      exact ⟨rfl, relation.publish_none input output, rfl,
        consistent, rfl, realValues, idealStep.1⟩
  | none =>
      rw [coordinate_real_terminal_recognized initial terminal function real.full realHashes realCoordinates
        state.supply flag input message cached fullRecognized (RandomOracle.eager hashFunction),
        PMF.mem_support_map_iff] at realSupport
      obtain ⟨realResponse, realReachable, rfl⟩ := realSupport
      have realStep := RandomOracle.eager_step_values hashFunction realHashes realValues message realResponse realReachable
      have terminalRelation : LatentDataRelation function ((input, realResponse.2) :: real.full) state := by
        rw [sound.1]
        exact relation.terminal_row input.1 terminal realResponse.2
      have same : realResponse.2 = idealResponse.2 := realStep.2.trans idealStep.2.symm
      rw [← same]
      exact ⟨rfl, terminalRelation.publish_none input realResponse.2, rfl,
        RandomOracle.TableConsistent.cons consistent input realResponse.2 cached, rfl, realStep.1, idealStep.1⟩

/-- An unrecognized terminal is genuinely fresh in the full real table by
the hidden-terminal completeness invariant. Both actual worlds allocate the
same next coordinate; no freshness conclusion is assumed as a premise here. -/
theorem coordinate_orphan_terminal_pair (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (real : TrackedRealState Payload Digest)
    (state : LatentState Payload Digest Label) (publicSame : real.exposed = state.exposed)
    (publicConsistent : PublicConsistent real) (paths : ExposedPaths initial real)
    (good : ForwardFresh initial real.full) (hiddenComplete : HiddenTerminalsComplete initial terminal real)
    (relation : LatentDataRelation function real.full state)
    (consistent : RandomOracle.TableConsistent real.full)
    (allocation : state.AllocationValid) (freshSupply : state.FreshSupply)
    (realHashes idealHashes : RandomOracle.Table (List Payload) Digest)
    (realCoordinates : RandomOracle.Table Label Digest) (flag : Bool)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (value : Digest) (block : Payload) (child : Label) (rest : List Label)
    (supply : state.supply = child :: rest) (privateFresh : realCoordinates.lookup child = none)
    (fresh : state.exposed.lookup (value, (true, block)) = none)
    (unrecognized : terminalMessage initial terminal state.exposed (value, (true, block)) = none)
    (noGuess : ∀ label, state.revealed.lookup label = none → function label ≠ value)
    (realAnswer : CoordinateRealState Payload Digest Label × Digest)
    (idealAnswer : LatentWorldState Payload Digest Label × Digest)
    (realSupport : realAnswer ∈ (coordinateRealWorld initial terminal (RandomOracle.eager function) hashOracle
      (real.full, ((state.supply, flag), (realHashes, realCoordinates))) (.inr (value, (true, block)))).support)
    (idealSupport : idealAnswer ∈ (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle
      (state, (idealHashes, state.revealed)) (.inr (value, (true, block)))).support) :
    realAnswer.2 = idealAnswer.2 ∧
    LatentDataRelation function realAnswer.1.1 idealAnswer.1.1 ∧
    realAnswer.1.2.1.1 = idealAnswer.1.1.supply ∧
    RandomOracle.TableConsistent realAnswer.1.1 := by
  let reserved : LatentState Payload Digest Label := {state with supply := rest}
  have fullUnrecognized : terminalMessage initial terminal real.full (value, (true, block)) = none :=
    (relation.terminal_recognition publicSame initial terminal good publicConsistent paths _ noGuess).trans unrecognized
  have fullFresh := hiddenComplete.unrecognized_fresh good (value, (true, block)) rfl
    (by rwa [publicSame]) fullUnrecognized
  have pending := freshSupply child (by rw [supply]; exact List.mem_cons_self)
  have choice : chooseLatent initial state (value, (true, block)) = (reserved, some child) := by
    simp [chooseLatent, reserveLabel, supply, reserved]
  have realExecution : coordinateRealWorld initial terminal (RandomOracle.eager function) hashOracle
      (real.full, ((state.supply, flag), (realHashes, realCoordinates))) (.inr (value, (true, block))) =
      PMF.pure ((((value, (true, block)), function child) :: real.full,
        ((rest, flag), (realHashes, (child, function child) :: realCoordinates))), function child) := by
    rw [coordinate_real_public_execution, supply]
    exact coordinate_real_local_fresh initial terminal function real.full realHashes realCoordinates
      child rest flag (value, (true, block)) fullFresh fullUnrecognized privateFresh hashOracle
  have idealExecution : latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle
      (state, (idealHashes, state.revealed)) (.inr (value, (true, block))) =
      PMF.pure ((finishLatent reserved (value, (true, block)) (some child) (function child),
        (idealHashes, (child, function child) :: state.revealed)), function child) := by
    simp only [List.lookup_eq_findSome?, beq_iff_eq] at fresh pending
    simp [latentCoordinateWorld, Program.statefulOracle, latentProgram, List.lookup_eq_findSome?, beq_iff_eq,
      fresh, unrecognized, choice, Program.run, Program.adaptOracle, latentContextRequest,
      RandomOracle.withContext, RandomOracle.eager, pending, PMF.pure_map]
  rw [realExecution, PMF.mem_support_pure_iff] at realSupport
  subst realAnswer
  rw [idealExecution, PMF.mem_support_pure_iff] at idealSupport
  subst idealAnswer
  have reservedRelation : LatentDataRelation function real.full reserved :=
    ⟨relation.sound, relation.complete, relation.published⟩
  have terminalRelation := reservedRelation.terminal_row value block (function child)
  refine ⟨rfl, ?_, ?_, RandomOracle.TableConsistent.cons consistent _ _ fullFresh⟩
  · apply terminalRelation.publish_orphan
    intro edge member equal
    apply allocation.2 edge member
    rw [equal, supply]
    exact List.mem_cons_self
  · have unused : child ∉ rest := (List.nodup_cons.mp (supply ▸ allocation.1)).1
    exact (finishLatent_supply_of_not_mem reserved (value, (true, block)) child (function child) unused).symm

/-- Any supported public symbolic call updates its exposed table by the same
record operation as the tracked real world. Reservation and coordinate choices
are hidden and cannot add extra public entries. -/
theorem latent_coordinate_public_record (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : LatentWorldState Payload Digest Label) (input : CompressionInput Payload Digest)
    (answer : LatentWorldState Payload Digest Label × Digest)
    (support : answer ∈ (latentCoordinateWorld initial terminal coordinates hashOracle state (.inr input)).support) :
    answer.1.1.exposed = rememberPublic state.1.exposed input answer.2 := by
  cases cached : state.1.exposed.lookup input with
  | some output =>
      rw [latent_coordinate_public_known initial terminal coordinates hashOracle state input output cached,
        PMF.mem_support_pure_iff] at support
      subst answer
      simp only [rememberPublic, cached]
  | none =>
      cases recognized : terminalMessage initial terminal state.1.exposed input with
      | some message =>
          rw [latent_coordinate_terminal_execution initial terminal coordinates hashOracle state.1
            state.2.1 state.2.2 input message cached recognized, PMF.mem_support_map_iff] at support
          obtain ⟨response, _, rfl⟩ := support
          simp only [rememberPublic, cached]
      | none =>
          unfold latentCoordinateWorld Program.statefulOracle at support
          rw [PMF.mem_support_map_iff] at support
          obtain ⟨out, reachable, rfl⟩ := support
          simp only [List.lookup_eq_findSome?, beq_iff_eq] at cached
          simp only [latentProgram, List.lookup_eq_findSome?, beq_iff_eq, cached, recognized,
            Program.run, PMF.mem_support_bind_iff] at reachable
          obtain ⟨response, _, tailSupport⟩ := reachable
          rw [PMF.mem_support_map_iff] at tailSupport
          obtain ⟨tail, tailSupport, rfl⟩ := tailSupport
          simp only [PMF.mem_support_pure_iff] at tailSupport
          subst tail
          have frame := chooseLatent_frame initial state.1 input
          cases (chooseLatent initial state.1 input).2 <;>
            simp only [finishLatent, frame.exposed, rememberPublic, List.lookup_eq_findSome?,
              beq_iff_eq, cached]

/-- Every actual coordinate-ideal interaction has the same public-cache fold
as the real instrumentation, for arbitrary independent backend kernels. -/
theorem latent_coordinate_public_history {Result : Type} (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (attack : Program (WorldInput Payload Digest) Digest Result) (state : LatentWorldState Payload Digest Label)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentCoordinateWorld initial terminal coordinates hashOracle) state).support) :
    out.state.1.exposed = publicHistory state.1.exposed out.trace := by
  apply Program.run_observe_trace (latentCoordinateWorld initial terminal coordinates hashOracle)
    (fun state => state.1.exposed)
    (fun seen request output => match request with
      | .inl _ => seen
      | .inr input => rememberPublic seen input output) _ attack state out support
  intro before request answer reachable
  cases request with
  | inr input => exact latent_coordinate_public_record initial terminal coordinates hashOracle before input answer reachable
  | inl message =>
      rw [latent_coordinate_high_execution, PMF.mem_support_map_iff] at reachable
      obtain ⟨response, _, rfl⟩ := reachable
      exact (reserveMessage_frame initial before.1 (.inl initial) message).exposed

/-- Equal outer histories imply equal public tables, even when all other
states and backend hash caches differ. No collision assumptions are needed. -/
theorem tracked_latent_public_same {Result : Type} (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (realStart : TrackedRealState Payload Digest) (idealStart : LatentWorldState Payload Digest Label)
    (initialSame : realStart.exposed = idealStart.1.exposed)
    (realOut : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest))
    (idealOut : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (realSupport : realOut ∈ (attack.run (trackedRealWorld initial terminal) realStart).support)
    (idealSupport : idealOut ∈ (attack.run (latentCoordinateWorld initial terminal coordinates hashOracle) idealStart).support)
    (traces : realOut.trace = idealOut.trace) : realOut.state.exposed = idealOut.state.1.exposed := by
  rw [trackedReal_public_history initial terminal attack realStart realOut realSupport,
    latent_coordinate_public_history initial terminal coordinates hashOracle attack idealStart idealOut idealSupport,
    initialSame, traces]

/-- At equal-history prefixes of the actual coordinate worlds there is an
original tracked-real witness with the same complete full-table outcome and
the ideal controller's exact public table. Public consistency and completeness
of hidden terminals transfer without any probability or no-guess assertion. -/
theorem coordinate_equal_history_witness {Result : Type} (initial : Digest) (terminal : Payload)
    (realCoordinates idealCoordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (realHashOracle idealHashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (backend : RealCoordinateState Payload Digest Label) (supply : List Label)
    (idealHashes : RandomOracle.Table (List Payload) Digest) (idealTable : RandomOracle.Table Label Digest)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (realOut : Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label))
    (idealOut : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (realSupport : realOut ∈ (attack.run (coordinateRealWorld initial terminal realCoordinates realHashOracle)
      ([], backend)).support)
    (idealSupport : idealOut ∈ (attack.run (latentCoordinateWorld initial terminal idealCoordinates idealHashOracle)
      (LatentState.empty supply, (idealHashes, idealTable))).support)
    (traces : realOut.trace = idealOut.trace) :
    ∃ tracked : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest),
      tracked ∈ (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty).support ∧
      Program.mapState TrackedRealState.full tracked = Program.mapState Prod.fst realOut ∧
      tracked.state.exposed = idealOut.state.1.exposed ∧
      PublicConsistent tracked.state ∧ HiddenTerminalsComplete initial terminal tracked.state := by
  obtain ⟨tracked, reachable, same⟩ := coordinate_real_tracked_witness initial terminal realCoordinates backend
    attack realOut realSupport
  have traceSame : tracked.trace = idealOut.trace := (congrArg Outcome.trace same).trans traces
  have publicSame := tracked_latent_public_same initial terminal idealCoordinates idealHashOracle attack
    TrackedRealState.empty (LatentState.empty supply, (idealHashes, idealTable)) rfl
    tracked idealOut reachable idealSupport traceSame
  exact ⟨tracked, reachable, same, publicSame,
    trackedReal_run_consistent initial terminal attack TrackedRealState.empty
      (by intro entry member; cases member) tracked reachable,
    trackedReal_hidden_terminals_from_empty initial terminal attack tracked reachable⟩

/-- Extend a genuine real proof record through an actual paired outer step.
Response equality is supplied by the concrete query-case correspondence; the
public table, no-guess flag, and exposed-path metadata are derived here rather
than assumed for the next state. This is a local induction step, not a claim
that the full paired data relation has already been preserved. -/
theorem coordinate_paired_tracked_step [Fintype Label]
    (initial : Digest) (terminal : Payload) (function : Label → Digest)
    (realCoordinates idealCoordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (realHash idealHash : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (real : TrackedRealState Payload Digest)
    (source : CoordinateRealState Payload Digest Label) (ideal : LatentWorldState Payload Digest Label)
    (fullSame : real.full = source.1) (publicSame : real.exposed = ideal.1.exposed)
    (relation : LatentDataRelation function real.full ideal.1)
    (publicConsistent : PublicConsistent real) (paths : ExposedPaths initial real)
    (complete : HiddenTerminalsComplete initial terminal real) (notGuessed : real.guessed = false)
    (request : WorldInput Payload Digest) (noHit : latentGuessHit function ideal request = false)
    (realAnswer : CoordinateRealState Payload Digest Label × Digest)
    (idealAnswer : LatentWorldState Payload Digest Label × Digest)
    (realSupport : realAnswer ∈ (coordinateRealWorld initial terminal realCoordinates realHash source request).support)
    (idealSupport : idealAnswer ∈ (latentCoordinateWorld initial terminal idealCoordinates idealHash ideal request).support)
    (responses : realAnswer.2 = idealAnswer.2) (good : ForwardFresh initial realAnswer.1.1) :
    ∃ trackedAnswer : TrackedRealState Payload Digest × Digest,
      trackedAnswer ∈ (trackedRealWorld initial terminal real request).support ∧
      (trackedAnswer.1.full, trackedAnswer.2) = (realAnswer.1.1, realAnswer.2) ∧
      trackedAnswer.1.exposed = idealAnswer.1.1.exposed ∧
      PublicConsistent trackedAnswer.1 ∧ HiddenTerminalsComplete initial terminal trackedAnswer.1 ∧
      trackedAnswer.1.guessed = false ∧ ExposedPaths initial trackedAnswer.1 := by
  have projected := coordinate_real_step_support initial terminal realCoordinates source request realAnswer realSupport
  rw [← fullSame, ← trackedRealWorld_project initial terminal real request, PMF.mem_support_map_iff] at projected
  obtain ⟨trackedAnswer, reachable, same⟩ := projected
  have fullAfter : trackedAnswer.1.full = realAnswer.1.1 := congrArg Prod.fst same
  have responseAfter : trackedAnswer.2 = idealAnswer.2 := (congrArg Prod.snd same).trans responses
  have metadata := relation.tracked_step_paths initial terminal publicSame publicConsistent paths notGuessed
    ideal.2 request noHit trackedAnswer reachable (by rwa [fullAfter])
  have publicAfter : trackedAnswer.1.exposed = idealAnswer.1.1.exposed := by
    cases request with
    | inl message =>
        rw [trackedRealWorld, PMF.mem_support_map_iff] at reachable
        obtain ⟨out, _, rfl⟩ := reachable
        rw [latent_coordinate_high_execution initial terminal idealCoordinates idealHash ideal.1 ideal.2.1 ideal.2.2 message,
          PMF.mem_support_map_iff] at idealSupport
        obtain ⟨answer, _, rfl⟩ := idealSupport
        exact publicSame.trans (reserveMessage_frame initial ideal.1 (.inl initial) message).exposed.symm
    | inr input =>
        have recorded := latent_coordinate_public_record initial terminal idealCoordinates idealHash ideal input idealAnswer idealSupport
        rw [trackedRealWorld, PMF.mem_support_map_iff] at reachable
        obtain ⟨answer, _, rfl⟩ := reachable
        rw [recorded, ← responseAfter, ← publicSame]
  exact ⟨trackedAnswer, reachable, same, publicAfter,
    trackedReal_step_consistent initial terminal real publicConsistent request trackedAnswer reachable,
    trackedReal_step_hidden_terminals initial terminal real publicConsistent complete request trackedAnswer reachable,
    metadata.1, metadata.2⟩

end Foundation.Hash
