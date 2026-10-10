import Foundation.Constructions.Hash.Indifferentiability
import Foundation.Constructions.Hash.TrackedReal
import Foundation.Crypto.Semantics.Oracle.StateMap
import Foundation.Crypto.Semantics.Oracle.RandomOracleContext

/-! A symbolic ideal experiment. Hidden data vertices are labels, not digest
values. Reserving a data path makes no coordinate query; a coordinate is queried
only when it is returned through the compression interface. The controller is
proof instrumentation, not a stronger simulator given the high-level log.
Its projected public behavior must be proved equal to the fixed candidate. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label]
  [Fintype Digest] [Nonempty Digest]

local instance latentCompressionBEq : BEq (CompressionInput Payload Digest) := instBEqOfDecidableEq
local instance latentGraphBEq : BEq ((Digest ⊕ Label) × Payload) := instBEqOfDecidableEq
local instance latentLabelBEq : BEq Label := instBEqOfDecidableEq

structure LatentState (Payload Digest Label : Type) where
  exposed : CompressionTable Payload Digest
  graph : RandomOracle.Table ((Digest ⊕ Label) × Payload) Label
  revealed : RandomOracle.Table Label Digest
  supply : List Label
  overflow : Bool

def LatentState.empty (supply : List Label) : LatentState Payload Digest Label :=
  ⟨[], [], [], supply, false⟩

/-- The remaining labels have not been queried of the coordinate oracle. -/
def LatentState.FreshSupply (state : LatentState Payload Digest Label) : Prop :=
  ∀ label ∈ state.supply, state.revealed.lookup label = none

/-- Reserve a coordinate without sampling or inspecting its value. Exhaustion
is recorded explicitly; it is not ruled out by an implicit resource assumption. -/
def reserveLabel (state : LatentState Payload Digest Label) :
    LatentState Payload Digest Label × Option Label :=
  match state.supply with
  | [] => ({ state with overflow := true }, none)
  | label :: rest => ({ state with supply := rest }, some label)

/-- A high-level data step follows or reserves a symbolic edge. -/
def latentAdvance (initial : Digest) (state : LatentState Payload Digest Label)
    (parent : Digest ⊕ Label) (block : Payload) : LatentState Payload Digest Label × (Digest ⊕ Label) :=
  match state.graph.lookup (parent, block) with
  | some child => (state, .inr child)
  | none =>
      let allocated := reserveLabel state
      match allocated.2 with
      | some child => ({ allocated.1 with graph := ((parent, block), child) :: allocated.1.graph }, .inr child)
      | none => (allocated.1, .inl initial)

/-- This entire data loop uses labels alone. No digest-coordinate oracle is
called by high-level processing of internal data blocks. -/
def reserveMessage (initial : Digest) (state : LatentState Payload Digest Label)
    (parent : Digest ⊕ Label) : List Payload → LatentState Payload Digest Label
  | [] => state
  | block :: rest =>
      let advanced := latentAdvance initial state parent block
      reserveMessage initial advanced.1 advanced.2 rest

/-- Only digests already returned by coordinate queries can identify a labelled
parent. All other input chaining values are treated as explicit fixed values. -/
def latentParent (initial : Digest) (state : LatentState Payload Digest Label) (value : Digest) : Digest ⊕ Label :=
  if value = initial then .inl initial else
    match (state.revealed.map (fun entry => (entry.2, entry.1))).lookup value with
    | some label => .inr label
    | none => .inl value

/-- An unrecognized public call may reveal a pending symbolic child. A child
already revealed is never queried again as fresh randomness. -/
def chooseLatent (initial : Digest) (state : LatentState Payload Digest Label)
    (input : CompressionInput Payload Digest) : LatentState Payload Digest Label × Option Label :=
  if input.2.1 = false then
    let parent := latentParent initial state input.1
    match state.graph.lookup (parent, input.2.2) with
    | some child =>
        if state.revealed.lookup child = none then (state, some child) else reserveLabel state
    | none =>
        let allocated := reserveLabel state
        match allocated.2 with
        | some child => ({ allocated.1 with graph := ((parent, input.2.2), child) :: allocated.1.graph }, some child)
        | none => allocated
  else reserveLabel state

/-- A public response is cached. Revealing a label also removes it from the
remaining supply, including malformed initial supplies with duplicate labels. -/
def finishLatent (state : LatentState Payload Digest Label)
    (input : CompressionInput Payload Digest) (selected : Option Label) (output : Digest) :
    LatentState Payload Digest Label :=
  match selected with
  | none => { state with exposed := (input, output) :: state.exposed }
  | some label =>
      { state with
        exposed := (input, output) :: state.exposed
        revealed := (label, output) :: state.revealed
        supply := state.supply.filter (fun other => other != label) }

abbrev LatentRequest (Payload Label : Type) := List Payload ⊕ Option Label

/-- High calls only reserve symbolic data edges before querying the shared
ideal hash. Low calls reuse the candidate's actual terminal recognizer. -/
def latentProgram (initial : Digest) (terminal : Payload)
    (state : LatentState Payload Digest Label) (request : WorldInput Payload Digest) :
    Program (LatentRequest Payload Label) Digest (LatentState Payload Digest Label × Digest) :=
  match request with
  | .inl message =>
      let reserved := reserveMessage initial state (.inl initial) message
      .query (.inl message) (fun output => .done (reserved, output))
  | .inr input =>
      match state.exposed.lookup input with
      | some output => .done (state, output)
      | none =>
          match terminalMessage initial terminal state.exposed input with
          | some message => .query (.inl message) (fun output =>
              .done ({ state with exposed := (input, output) :: state.exposed }, output))
          | none =>
              let choice := chooseLatent initial state input
              .query (.inr choice.2) (fun output => .done (finishLatent choice.1 input choice.2 output, output))

/-- The two independent backend windows share no hidden state with each other.
An exhausted supply uses an explicit local uniform draw, not an aliased label. -/
noncomputable def latentBackend
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    Oracle (LatentRequest Payload Label) Digest
      (RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest) :=
  fun (hashes, coordinates) request => match request with
  | .inl message => (hashOracle hashes message).map (fun answer => ((answer.1, coordinates), answer.2))
  | .inr (some label) => (RandomOracle.oracle coordinates label).map (fun answer => ((hashes, answer.1), answer.2))
  | .inr none => (uniform Digest).map (fun output => ((hashes, coordinates), output))

noncomputable def latentWorld (initial : Digest) (terminal : Payload)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    Oracle (WorldInput Payload Digest) Digest
      (LatentState Payload Digest Label ×
        (RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest)) :=
  Program.statefulOracle (latentProgram initial terminal) (latentBackend hashOracle)

/-- Reserving symbolic paths preserves all observed values and only consumes
unused labels. This is a frame property, not a hidden-value independence claim. -/
structure LatentFrame (before after : LatentState Payload Digest Label) : Prop where
  exposed : after.exposed = before.exposed
  revealed : after.revealed = before.revealed
  supply : after.supply ⊆ before.supply

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem LatentFrame.trans {before middle after : LatentState Payload Digest Label}
    (first : LatentFrame before middle) (last : LatentFrame middle after) : LatentFrame before after :=
  ⟨last.exposed.trans first.exposed, last.revealed.trans first.revealed, fun _ member => first.supply (last.supply member)⟩

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
theorem LatentFrame.freshSupply {before after : LatentState Payload Digest Label}
    (frame : LatentFrame before after) (fresh : before.FreshSupply) : after.FreshSupply := by
  intro label member
  rw [frame.revealed]
  exact fresh label (frame.supply member)

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label] [Fintype Digest] [Nonempty Digest] in
theorem reserveLabel_frame (state : LatentState Payload Digest Label) :
    LatentFrame state (reserveLabel state).1 := by
  cases supply : state.supply with
  | nil =>
      simp only [reserveLabel, supply]
      exact ⟨rfl, rfl, by simp [supply]⟩
  | cons label rest =>
      simp only [reserveLabel, supply]
      refine ⟨rfl, rfl, ?_⟩
      intro other member
      rw [supply]
      exact List.mem_cons_of_mem _ member

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
theorem reserveLabel_fresh (state : LatentState Payload Digest Label) (fresh : state.FreshSupply)
    (label : Label) (selected : (reserveLabel state).2 = some label) : state.revealed.lookup label = none := by
  cases supply : state.supply with
  | nil => simp [reserveLabel, supply] at selected
  | cons first rest =>
      simp only [reserveLabel, supply, Option.some.injEq] at selected
      subst label
      exact fresh first (by rw [supply]; exact List.mem_cons_self ..)

omit [Fintype Digest] [Nonempty Digest] in
theorem latentAdvance_frame (initial : Digest) (state : LatentState Payload Digest Label)
    (parent : Digest ⊕ Label) (block : Payload) : LatentFrame state (latentAdvance initial state parent block).1 := by
  unfold latentAdvance
  split
  · exact ⟨rfl, rfl, List.Subset.refl _⟩
  · dsimp only
    split
    · exact ⟨(reserveLabel_frame state).exposed, (reserveLabel_frame state).revealed,
        (reserveLabel_frame state).supply⟩
    · exact reserveLabel_frame state

omit [Fintype Digest] [Nonempty Digest] in
theorem reserveMessage_frame (initial : Digest) (state : LatentState Payload Digest Label)
    (parent : Digest ⊕ Label) (message : List Payload) : LatentFrame state (reserveMessage initial state parent message) := by
  induction message generalizing state parent with
  | nil => exact ⟨rfl, rfl, List.Subset.refl _⟩
  | cons block rest ih => exact (latentAdvance_frame initial state parent block).trans (ih _ _)

omit [Fintype Digest] [Nonempty Digest] in
theorem chooseLatent_frame (initial : Digest) (state : LatentState Payload Digest Label)
    (input : CompressionInput Payload Digest) : LatentFrame state (chooseLatent initial state input).1 := by
  unfold chooseLatent
  split
  · dsimp only
    split
    · split
      · exact ⟨rfl, rfl, List.Subset.refl _⟩
      · exact reserveLabel_frame state
    · split
      · exact ⟨(reserveLabel_frame state).exposed, (reserveLabel_frame state).revealed,
          (reserveLabel_frame state).supply⟩
      · exact reserveLabel_frame state
  · exact reserveLabel_frame state

omit [Fintype Digest] [Nonempty Digest] in
theorem chooseLatent_fresh (initial : Digest) (state : LatentState Payload Digest Label)
    (fresh : state.FreshSupply) (input : CompressionInput Payload Digest) (label : Label)
    (selected : (chooseLatent initial state input).2 = some label) : state.revealed.lookup label = none := by
  unfold chooseLatent at selected
  split at selected
  · dsimp only at selected
    split at selected
    · split at selected
      · rename_i child edge pending
        simp only [Option.some.injEq] at selected
        subst label
        exact pending
      · exact reserveLabel_fresh state fresh label selected
    · split at selected
      · rename_i child allocation
        simp only [Option.some.injEq] at selected
        subst label
        exact reserveLabel_fresh state fresh child allocation
      · exact reserveLabel_fresh state fresh label selected
  · exact reserveLabel_fresh state fresh label selected

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
theorem finishLatent_freshSupply (state : LatentState Payload Digest Label) (fresh : state.FreshSupply)
    (input : CompressionInput Payload Digest) (selected : Option Label) (output : Digest) :
    (finishLatent state input selected output).FreshSupply := by
  cases selected with
  | none => exact fresh
  | some label =>
      intro other member
      obtain ⟨old, different⟩ := List.mem_filter.mp member
      have different : other ≠ label := by simpa only [bne_iff_ne] using different
      simp [finishLatent, List.lookup_cons, beq_eq_false_iff_ne.mpr different, fresh other old]

/-- Exact execution law, derived from the symbolic controller's interpreter. -/
theorem latentWorld_eq (initial : Digest) (terminal : Payload)
    (state : LatentState Payload Digest Label)
    (hashes : RandomOracle.Table (List Payload) Digest) (coordinates : RandomOracle.Table Label Digest)
    (request : WorldInput Payload Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    latentWorld initial terminal hashOracle (state, (hashes, coordinates)) request =
      match request with
      | .inl message => (hashOracle hashes message).map (fun answer =>
          ((reserveMessage initial state (.inl initial) message, (answer.1, coordinates)), answer.2))
      | .inr input => match state.exposed.lookup input with
        | some output => PMF.pure ((state, (hashes, coordinates)), output)
        | none => match terminalMessage initial terminal state.exposed input with
          | some message => (hashOracle hashes message).map (fun answer =>
              (({ state with exposed := (input, answer.2) :: state.exposed }, (answer.1, coordinates)), answer.2))
          | none =>
              let choice := chooseLatent initial state input
              match choice.2 with
              | some label => (RandomOracle.oracle coordinates label).map (fun answer =>
                  ((finishLatent choice.1 input choice.2 answer.2, (hashes, answer.1)), answer.2))
              | none => (uniform Digest).map (fun output =>
                  ((finishLatent choice.1 input choice.2 output, (hashes, coordinates)), output)) := by
  cases request with
  | inl message =>
      simp [latentWorld, Program.statefulOracle, latentProgram, Program.run, latentBackend,
        PMF.pure_map, PMF.map_bind]
      rfl
  | inr input =>
      cases exposed : state.exposed.lookup input with
      | some output =>
          simp [latentWorld, Program.statefulOracle, latentProgram, exposed, Program.run, PMF.pure_map]
      | none =>
          cases terminalQuery : terminalMessage initial terminal state.exposed input with
          | some message =>
              simp [latentWorld, Program.statefulOracle, latentProgram, exposed, terminalQuery,
                Program.run, latentBackend, PMF.pure_map, PMF.map_bind]
              rfl
          | none =>
              cases selected : (chooseLatent initial state input).2 <;>
                simp [latentWorld, Program.statefulOracle, latentProgram, exposed, terminalQuery,
                  Program.run, latentBackend, selected, PMF.pure_map, PMF.map_bind] <;> rfl

omit [Fintype Digest] [Nonempty Digest] in
/-- High calls query only the ideal hash. Low calls make at most one backend
call, which is either the ideal hash, a coordinate, or a local draw. -/
theorem latentProgram_queries (initial : Digest) (terminal : Payload)
    (state : LatentState Payload Digest Label) (request : WorldInput Payload Digest) :
    (latentProgram initial terminal state request).BoundedQueries 1 := by
  cases request with
  | inl message => exact .query _ _ 0 (fun _ => .done _ 0)
  | inr input =>
      simp only [latentProgram]
      split
      · exact .done _ 1
      · split <;> exact .query _ _ 0 (fun _ => .done _ 0)

abbrev LatentWorldState (Payload Digest Label : Type) := LatentState Payload Digest Label ×
  (RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest)

/-- The controller's revealed values exactly agree with actual coordinate
queries. Its remaining supply consists only of unqueried coordinates. -/
def LatentCoherent (state : LatentWorldState Payload Digest Label) : Prop :=
  state.1.revealed = state.2.2 ∧ state.1.FreshSupply

/-- Erase symbolic instrumentation, retaining exactly the fixed candidate's
private compression table and the shared ideal hash table. -/
def latentView (state : LatentWorldState Payload Digest Label) :
    CompressionTable Payload Digest × RandomOracle.Table (List Payload) Digest :=
  (state.1.exposed, state.2.1)

/-- Backend/controller agreement is preserved through either public window,
including supply exhaustion and duplicate labels in an initial supply. -/
theorem latent_step_coherent (initial : Digest) (terminal : Payload)
    {hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)}
    (state : LatentWorldState Payload Digest Label) (valid : LatentCoherent state)
    (request : WorldInput Payload Digest) (answer : LatentWorldState Payload Digest Label × Digest)
    (support : answer ∈ (latentWorld initial terminal hashOracle state request).support) :
    LatentCoherent answer.1 := by
  rcases state with ⟨control, hashes, coordinates⟩
  rcases valid with ⟨agreement, fresh⟩
  dsimp only at agreement fresh
  rw [latentWorld_eq (hashOracle := hashOracle)] at support
  cases request with
  | inl message =>
      simp only at support
      rw [PMF.mem_support_map_iff] at support
      obtain ⟨result, _, rfl⟩ := support
      exact ⟨(reserveMessage_frame initial control (.inl initial) message).revealed.trans agreement,
        (reserveMessage_frame initial control (.inl initial) message).freshSupply fresh⟩
  | inr input =>
      simp only at support
      cases cached : control.exposed.lookup input with
      | some output =>
          simp only [cached, PMF.mem_support_pure_iff] at support
          subst answer
          exact ⟨agreement, fresh⟩
      | none =>
          simp only [cached] at support
          cases recognized : terminalMessage initial terminal control.exposed input with
          | some message =>
              simp only [recognized] at support
              rw [PMF.mem_support_map_iff] at support
              obtain ⟨result, _, rfl⟩ := support
              exact ⟨agreement, fresh⟩
          | none =>
              simp only [recognized] at support
              have frame := chooseLatent_frame initial control input
              have choiceFresh := frame.freshSupply fresh
              cases selected : (chooseLatent initial control input).2 with
              | none =>
                  simp only [selected] at support
                  rw [PMF.mem_support_map_iff] at support
                  obtain ⟨output, _, rfl⟩ := support
                  exact ⟨frame.revealed.trans agreement, choiceFresh⟩
              | some label =>
                  simp only [selected] at support
                  have coordinateFresh : coordinates.lookup label = none := by
                    rw [← agreement]
                    exact chooseLatent_fresh initial control fresh input label selected
                  rw [RandomOracle.fresh coordinates label coordinateFresh] at support
                  simp only [PMF.map_comp, Function.comp_def] at support
                  rw [PMF.mem_support_map_iff] at support
                  obtain ⟨output, _, rfl⟩ := support
                  refine ⟨?_, ?_⟩
                  · simp only [finishLatent]
                    exact congrArg (List.cons (label, output)) (frame.revealed.trans agreement)
                  · exact finishLatent_freshSupply _ choiceFresh input (some label) output

/-- Erasing the symbolic state gives exactly the original fixed simulator's
one-step distribution. No simulator is chosen as a function of the attacker. -/
theorem latent_step_project (initial : Digest) (terminal : Payload)
    (state : LatentWorldState Payload Digest Label) (valid : LatentCoherent state)
    (request : WorldInput Payload Digest) :
    (latentWorld initial terminal RandomOracle.oracle state request).map (fun answer => (latentView answer.1, answer.2)) =
      idealWorld RandomOracle.oracle initial terminal (latentView state) request := by
  rcases state with ⟨control, hashes, coordinates⟩
  rcases valid with ⟨agreement, fresh⟩
  dsimp only at agreement fresh
  rw [latentWorld_eq]
  cases request with
  | inl message =>
      simp only [idealWorld, latentView, PMF.map_comp, Function.comp_def]
      rw [(reserveMessage_frame initial control (.inl initial) message).exposed]
  | inr input =>
      simp only [idealWorld, latentView]
      rw [compressionSimulator_terminal_eq]
      -- Both legal equality implementations of compression keys agree.
      simp only [List.lookup_eq_findSome?, Bool.beq_eq_decide_eq, decide_eq_true_eq]
      cases cached : control.exposed.lookup input with
      | some output =>
          simp only [List.lookup_eq_findSome?, Bool.beq_eq_decide_eq, decide_eq_true_eq] at cached
          simp [cached, PMF.pure_map]
      | none =>
          simp only [List.lookup_eq_findSome?, Bool.beq_eq_decide_eq, decide_eq_true_eq] at cached
          simp only [cached]
          cases recognized : terminalMessage initial terminal control.exposed input with
          | some message => simp [PMF.map_comp, Function.comp_def]
          | none =>
              have frame := chooseLatent_frame initial control input
              cases selected : (chooseLatent initial control input).2 with
              | none => simp [PMF.map_comp, Function.comp_def, finishLatent, frame.exposed]
              | some label =>
                  have coordinateFresh : coordinates.lookup label = none := by
                    rw [← agreement]
                    exact chooseLatent_fresh initial control fresh input label selected
                  simp [RandomOracle.fresh coordinates label coordinateFresh,
                    PMF.map_comp, Function.comp_def, finishLatent, frame.exposed]

/-- Agreement holds throughout every adaptive interaction, not just along a
fixed nonadaptive list of messages. -/
theorem latent_run_coherent {Result : Type} (initial : Digest) (terminal : Payload)
    {hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)}
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : LatentWorldState Payload Digest Label) (valid : LatentCoherent state)
    (out : Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label))
    (support : out ∈ (attack.run (latentWorld initial terminal hashOracle) state).support) :
    LatentCoherent out.state :=
  Program.run_preserves _ LatentCoherent (latent_step_coherent initial terminal) attack state valid out support

/-- Exact equality includes the result, the projected final state, and the
entire public interaction transcript. Internal coordinate queries stay private. -/
theorem latent_run_project {Result : Type} (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : LatentWorldState Payload Digest Label) (valid : LatentCoherent state) :
    (attack.run (latentWorld initial terminal) state).map (Program.mapState latentView) =
      attack.run (idealWorld RandomOracle.oracle initial terminal) (latentView state) :=
  Program.run_state_map_of_invariant latentView _ _ LatentCoherent
    (latent_step_coherent initial terminal) (latent_step_project initial terminal) attack state valid

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
theorem latent_empty_coherent (supply : List Label) :
    LatentCoherent (Payload := Payload) (LatentState.empty supply, ([], ([] : RandomOracle.Table Label Digest))) := by
  exact ⟨rfl, fun _ _ => rfl⟩

/-- Any supply gives the same public law as the single fixed candidate. The
supply has no adversary-dependent simulator choice hidden in its quantifiers. -/
theorem latent_candidate_run {Result : Type} (initial : Digest) (terminal : Payload)
    (supply : List Label) (attack : Program (WorldInput Payload Digest) Digest Result) :
    (attack.run (latentWorld initial terminal) (LatentState.empty supply, ([], []))).map
        (Program.mapState latentView) =
      attack.run ((candidate initial terminal).world RandomOracle.oracle) ([], []) := by
  rw [candidate_world]
  exact latent_run_project initial terminal attack _ (latent_empty_coherent supply)

/-- This is compilation into Foundation's oracle syntax. It preserves joint
private state, backend state and result; it is not a machine-time certificate. -/
theorem latent_inline_run {Result : Type} (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : LatentState Payload Digest Label)
    (backend : RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest) :
    ((Program.inlineState (latentProgram initial terminal) state attack).run latentBackend backend).map
        Program.resultState =
      (attack.run (latentWorld initial terminal) (state, backend)).map
        (fun out => (out.state.2, (out.state.1, out.result))) :=
  Program.inlineState_run (latentProgram initial terminal) attack latentBackend state backend

/-- Context requests consist of ideal-hash queries and local draws. Finite
coordinate requests use the other independent window. -/
def latentContextRequest : LatentRequest Payload Label → SimulatorRequest Payload ⊕ Label
  | .inl message => .inl (.inl message)
  | .inr none => .inl (.inr ())
  | .inr (some label) => .inr label

omit [DecidableEq Digest] in
/-- The context factorization is an equality of actual backend kernels. -/
theorem latent_backend_context
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    Program.adaptOracle (latentContextRequest (Payload := Payload) (Label := Label)) id
      (RandomOracle.withContext (simulatorBackend hashOracle) RandomOracle.oracle) =
        (latentBackend hashOracle : Oracle (LatentRequest Payload Label) Digest
          (RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest)) := by
  funext state request
  rcases state with ⟨hashes, coordinates⟩
  cases request with
  | inl message => simp [Program.adaptOracle, latentContextRequest, RandomOracle.withContext,
      simulatorBackend, latentBackend, PMF.map_comp, Function.comp_def]
  | inr label => cases label <;>
      simp [Program.adaptOracle, latentContextRequest, RandomOracle.withContext,
        simulatorBackend, latentBackend, PMF.map_comp, Function.comp_def]

/-- Compile the controller and put its two independent backend windows in the
interface used by the finite-coordinate posterior theorem. -/
def latentCompiled {Result : Type} (initial : Digest) (terminal : Payload)
    (state : LatentState Payload Digest Label) (attack : Program (WorldInput Payload Digest) Digest Result) :
    Program (SimulatorRequest Payload ⊕ Label) Digest (LatentState Payload Digest Label × Result) :=
  (Program.inlineState (latentProgram initial terminal) state attack).mapQueries latentContextRequest id

/-- Parameterize the independent coordinate and hash kernels. The original
lazy hash remains the default; the symbolic controller is unchanged. -/
noncomputable def latentCoordinateWorld (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    Oracle (WorldInput Payload Digest) Digest (LatentWorldState Payload Digest Label) :=
  Program.statefulOracle (latentProgram initial terminal)
    (Program.adaptOracle latentContextRequest id
      (RandomOracle.withContext (simulatorBackend hashOracle) coordinates))

/-- Lazy coordinates recover the previously verified symbolic experiment. -/
theorem latent_coordinate_lazy (initial : Digest) (terminal : Payload)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    latentCoordinateWorld initial terminal (RandomOracle.oracle (Input := Label)) hashOracle =
      (latentWorld initial terminal hashOracle : Oracle (WorldInput Payload Digest) Digest
        (LatentWorldState Payload Digest Label)) := by
  unfold latentCoordinateWorld
  rw [latent_backend_context hashOracle]
  rfl

/-- Compilation preserves the joint state/result law for either eager or lazy
coordinates; the statement imposes no randomness assumption on that backend. -/
theorem latent_compiled_coordinates {Result : Type} (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : LatentState Payload Digest Label)
    (backend : RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    ((latentCompiled initial terminal state attack).run
        (RandomOracle.withContext (simulatorBackend hashOracle) coordinates) backend).map
        Program.resultState =
      (attack.run (latentCoordinateWorld initial terminal coordinates hashOracle) (state, backend)).map
        (fun out => (out.state.2, (out.state.1, out.result))) := by
  have mapped := congrArg (PMF.map Program.resultState)
    (Program.mapQueries_run latentContextRequest id
      (Program.inlineState (latentProgram initial terminal) state attack)
      (RandomOracle.withContext (simulatorBackend hashOracle) coordinates) backend)
  simp only [PMF.map_comp, Program.mapTranscript, Program.resultState, Function.comp_def, id_eq] at mapped
  exact mapped.trans (Program.inlineState_run (latentProgram initial terminal) attack _ state backend)

/-- The compiled experiment retains exactly the original joint backend state,
controller state and result. This connects the posterior theorem to actual code
in Foundation's oracle syntax, rather than a separately postulated experiment. -/
theorem latent_compiled_run {Result : Type} (initial : Digest) (terminal : Payload)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : LatentState Payload Digest Label)
    (backend : RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    ((latentCompiled initial terminal state attack).run
        (RandomOracle.withContext (simulatorBackend hashOracle) RandomOracle.oracle) backend).map
        Program.resultState =
      (attack.run (latentWorld initial terminal hashOracle) (state, backend)).map
        (fun out => (out.state.2, (out.state.1, out.result))) := by
  simpa only [latent_coordinate_lazy] using
    latent_compiled_coordinates initial terminal attack state backend RandomOracle.oracle hashOracle

/-- Every reachable compiled result preserves controller/backend agreement. -/
theorem latent_compiled_coherent {Result : Type} (initial : Digest) (terminal : Payload)
    {hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest)}
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : LatentState Payload Digest Label)
    (backend : RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest)
    (valid : LatentCoherent (state, backend))
    (out : Outcome (SimulatorRequest Payload ⊕ Label) Digest (LatentState Payload Digest Label × Result)
      (RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest))
    (support : out ∈ ((latentCompiled initial terminal state attack).run
      (RandomOracle.withContext (simulatorBackend hashOracle) RandomOracle.oracle) backend).support) :
    LatentCoherent (out.result.1, out.state) := by
  have observed : Program.resultState out ∈ (((latentCompiled initial terminal state attack).run
      (RandomOracle.withContext (simulatorBackend hashOracle) RandomOracle.oracle) backend).map
      Program.resultState).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨out, support, rfl⟩
  rw [latent_compiled_run (hashOracle := hashOracle), PMF.mem_support_map_iff] at observed
  obtain ⟨worldOut, reachable, same⟩ := observed
  have backendSame := congrArg Prod.fst same
  have controlSame := congrArg (fun pair => pair.2.1) same
  dsimp only [Program.resultState] at backendSame controlSame
  rw [← backendSame, ← controlSame]
  exact latent_run_coherent initial terminal attack (state, backend) valid worldOut reachable

/-- A hidden coordinate chosen from the complete compiled execution is uniform
jointly with that execution, provided the controller still marks it unrevealed.
Only Label is finite; messages and the ideal-hash state remain unrestricted. -/
theorem latent_unrevealed_joint [Fintype Label] {Result : Type}
    (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (choose : Outcome (SimulatorRequest Payload ⊕ Label) Digest (LatentState Payload Digest Label × Result)
      (RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest) → Label)
    (pending : ∀ out ∈ ((latentCompiled initial terminal (LatentState.empty supply) attack).run
      (RandomOracle.withContext (simulatorBackend RandomOracle.oracle) RandomOracle.oracle) ([], [])).support,
      out.result.1.revealed.lookup (choose out) = none) :
    (uniform (Label → Digest)).bind (fun function =>
      ((latentCompiled initial terminal (LatentState.empty supply) attack).run
        (RandomOracle.withContext (simulatorBackend RandomOracle.oracle) (RandomOracle.eager function)) ([], [])).map
        (fun out => (out, function (choose out)))) =
    ((latentCompiled initial terminal (LatentState.empty supply) attack).run
      (RandomOracle.withContext (simulatorBackend RandomOracle.oracle) RandomOracle.oracle) ([], [])).bind (fun out =>
        (uniform Digest).map (fun value => (out, value))) := by
  apply RandomOracle.eager_unqueried_joint_context
  intro out support
  have coherent := latent_compiled_coherent initial terminal attack (LatentState.empty supply) ([], [])
    (latent_empty_coherent supply) out support
  have agreement : out.result.1.revealed = out.state.2 := coherent.1
  rw [← agreement]
  exact pending out support

omit [Fintype Digest] [Nonempty Digest] in
/-- A q-query public interaction compiles to at most q actual backend calls.
This counts ideal-hash queries, coordinate queries and local draws together. -/
theorem latent_compiled_queries {Result : Type} (initial : Digest) (terminal : Payload)
    (state : LatentState Payload Digest Label)
    {attack : Program (WorldInput Payload Digest) Digest Result} {q : Nat}
    (bound : attack.BoundedQueries q) : (latentCompiled initial terminal state attack).BoundedQueries q := by
  apply Program.mapQueries_queries
  simpa only [Nat.mul_one] using Program.inlineState_queries (latentProgram initial terminal)
    1 (latentProgram_queries initial terminal) bound state

/-- A duplicate-free list of every coordinate not revealed by this controller.
Reserved-but-hidden vertices are included; so are any unused supply labels. -/
noncomputable def unrevealedLabels [Fintype Label] (state : LatentState Payload Digest Label) : List Label :=
  Finset.univ.toList.filter (fun label => decide (state.revealed.lookup label = none))

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
theorem unrevealedLabels_fresh [Fintype Label] (state : LatentState Payload Digest Label)
    (label : Label) (member : label ∈ unrevealedLabels state) : state.revealed.lookup label = none := by
  exact of_decide_eq_true (List.mem_filter.mp member).2

omit [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest] in
theorem unrevealedLabels_length [Fintype Label] (state : LatentState Payload Digest Label) :
    (unrevealedLabels state).length ≤ Fintype.card Label := by
  exact (List.length_filter_le _ _).trans_eq (by simp)

/-- Actual finite-coordinate guessing bound for the compiled symbolic ideal
experiment. Guesses may depend on its entire reachable outcome. This does not
yet transfer the bound to the real compression experiment or its stopping flag. -/
theorem latent_unrevealed_guess_bound [Fintype Label] {Result : Type}
    (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle)
    (guesses : Outcome (SimulatorRequest Payload ⊕ Label) Digest (LatentState Payload Digest Label × Result)
      (RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest) → List Digest)
    (guessLimit : Nat)
    (size : ∀ out ∈ ((latentCompiled initial terminal (LatentState.empty supply) attack).run
      (RandomOracle.withContext (simulatorBackend hashOracle) RandomOracle.oracle) ([], [])).support,
      (guesses out).length ≤ guessLimit) :
    eventProb ((uniform (Label → Digest)).bind (fun function =>
      ((latentCompiled initial terminal (LatentState.empty supply) attack).run
        (RandomOracle.withContext (simulatorBackend hashOracle) (RandomOracle.eager function)) ([], [])).map
        (fun out => (out, function))))
      (fun pair => ∃ label ∈ unrevealedLabels pair.1.result.1, pair.2 label ∈ guesses pair.1) ≤
      ((Fintype.card Label * guessLimit : Nat) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  apply RandomOracle.eager_unqueried_many_guess_bound_context
    (simulatorBackend hashOracle) _ [] (fun out => unrevealedLabels out.result.1) guesses
    (Fintype.card Label) guessLimit
  · intro out support label member
    have coherent := latent_compiled_coherent initial terminal attack (LatentState.empty supply) ([], [])
      (latent_empty_coherent supply) out support
    have agreement : out.result.1.revealed = out.state.2 := coherent.1
    rw [← agreement]
    exact unrevealedLabels_fresh out.result.1 label member
  · intro out _
    exact unrevealedLabels_length out.result.1
  · exact size

/-- Resampling an unrevealed symbolic coordinate preserves its joint law with
all already observed compiled state. This is an internal proof operation. -/
theorem latent_unrevealed_resample [Fintype Label] {Result : Type}
    (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (choose : Outcome (SimulatorRequest Payload ⊕ Label) Digest (LatentState Payload Digest Label × Result)
      (RandomOracle.Table (List Payload) Digest × RandomOracle.Table Label Digest) → Label)
    (pending : ∀ out ∈ ((latentCompiled initial terminal (LatentState.empty supply) attack).run
      (RandomOracle.withContext (simulatorBackend RandomOracle.oracle) RandomOracle.oracle) ([], [])).support,
      out.result.1.revealed.lookup (choose out) = none) :
    (uniform (Label → Digest)).bind (fun function =>
      ((latentCompiled initial terminal (LatentState.empty supply) attack).run
        (RandomOracle.withContext (simulatorBackend RandomOracle.oracle) (RandomOracle.eager function)) ([], [])).bind
        (fun out => (uniform Digest).map (fun value => (out, Function.update function (choose out) value)))) =
    (uniform (Label → Digest)).bind (fun function =>
      ((latentCompiled initial terminal (LatentState.empty supply) attack).run
        (RandomOracle.withContext (simulatorBackend RandomOracle.oracle) (RandomOracle.eager function)) ([], [])).map
        (fun out => (out, function))) := by
  apply RandomOracle.eager_resample_unqueried_context
  intro out support
  have coherent := latent_compiled_coherent initial terminal attack (LatentState.empty supply) ([], [])
    (latent_empty_coherent supply) out support
  have agreement : out.result.1.revealed = out.state.2 := coherent.1
  rw [← agreement]
  exact pending out support

end Foundation.Hash
