import Foundation.Crypto.Semantics.Oracle.RandomOracle

/-! A local-to-global construction for deterministic replay of adaptive MAC
games. Each implementation executes independently from one retained function
and coin tape. Only a one-query response law and preservation of a local cache
invariant are inputs. No whole-program relation or joint realization is an
input. This is ordinary structural induction, not a higher-dimensional
separation theorem. The random-world law is supplied; fresh independent lazy
sampling marginals are NOT proved by this module. -/
namespace Foundation.Examples.RandomFunctionMACLocalRealization
open CryptoOracle

variable {Input Tag Result : Type}

structure Model (Input Tag : Type) where
  State : Type
  initial : State
  valid : (Input → Tag) → State → Prop
  step : (Input → Tag) → State → Input → State × Tag
  initial_valid : ∀ function, valid function initial
  step_valid : ∀ function state request, valid function state →
    valid function (step function state request).1 ∧
      (step function state request).2 = function request

structure Observation (Input Tag Result : Type) where
  result : Result
  transcript : List (Input × Tag)
  cursor : Nat
  deriving DecidableEq

structure Execution (Input Tag Result State : Type) where
  observation : Observation Input Tag Result
  state : State

def reference (function : Input → Tag) (coins : Nat → Bool) :
    Nat → Program Input Tag Result → Observation Input Tag Result
  | cursor, .done result => ⟨result, [], cursor⟩
  | cursor, .query request next =>
      let tail := reference function coins cursor (next (function request))
      { tail with transcript := (request, function request) :: tail.transcript }
  | cursor, .coin next => reference function coins (cursor + 1) (next (coins cursor))

def execute (model : Model Input Tag) (function : Input → Tag) (coins : Nat → Bool) :
    Nat → model.State → Program Input Tag Result → Execution Input Tag Result model.State
  | cursor, state, .done result => ⟨⟨result, [], cursor⟩, state⟩
  | cursor, state, .query request next =>
      let answer := model.step function state request
      let tail := execute model function coins cursor answer.1 (next answer.2)
      ⟨{ tail.observation with transcript := (request, answer.2) :: tail.observation.transcript },
        tail.state⟩
  | cursor, state, .coin next => execute model function coins (cursor + 1) state (next (coins cursor))

/-- The entire adaptive transcript, result, coin alignment and final invariant
are generated from the two one-step laws. The client supplies no global relation. -/
theorem execute_correct (model : Model Input Tag) (function : Input → Tag) (coins : Nat → Bool)
    (program : Program Input Tag Result) (cursor : Nat) (state : model.State)
    (valid : model.valid function state) :
    (execute model function coins cursor state program).observation = reference function coins cursor program ∧
      model.valid function (execute model function coins cursor state program).state := by
  induction program generalizing cursor state with
  | done result => exact ⟨rfl, valid⟩
  | coin next ih => exact ih (coins cursor) (cursor + 1) state valid
  | query request next ih =>
      obtain ⟨preserved, response⟩ := model.step_valid function state request valid
      obtain ⟨same, finalValid⟩ := ih (model.step function state request).2 cursor
        (model.step function state request).1 preserved
      constructor
      · simp only [execute, reference]
        rw [same, response]
      · exact finalValid

variable [DecidableEq Input]

/-- Representation laws mention one entry only. They do not compare programs. -/
structure Storage (Input Tag : Type) [DecidableEq Input] where
  State : Type
  empty : State
  lookup : State → Input → Option Tag
  put : State → Input → Tag → State
  empty_lookup : ∀ request, lookup empty request = none
  put_same : ∀ state request tag, lookup (put state request tag) request = some tag
  put_other : ∀ state request tag other, other ≠ request →
    lookup (put state request tag) other = lookup state other

def Storage.consistent (storage : Storage Input Tag) (function : Input → Tag)
    (state : storage.State) : Prop :=
  ∀ request tag, storage.lookup state request = some tag → tag = function request

theorem Storage.put_consistent (storage : Storage Input Tag) (function : Input → Tag)
    (state : storage.State) (valid : storage.consistent function state) (request : Input) :
    storage.consistent function (storage.put state request (function request)) := by
  intro other tag found
  by_cases same : other = request
  · subst other
    rw [storage.put_same] at found
    exact (Option.some.inj found).symm
  · rw [storage.put_other state request (function request) other same] at found
    exact valid other tag found

def Storage.model (storage : Storage Input Tag) (memo : Bool) : Model Input Tag where
  State := storage.State × List Input
  initial := (storage.empty, [])
  valid function state := storage.consistent function state.1
  step function state request :=
    match storage.lookup state.1 request with
    | some tag => ((state.1, if memo then state.2 else state.2 ++ [request]), tag)
    | none => ((storage.put state.1 request (function request), state.2 ++ [request]), function request)
  initial_valid := by
    intro function request tag found
    rw [storage.empty_lookup] at found
    contradiction
  step_valid := by
    intro function state request valid
    cases found : storage.lookup state.1 request with
    | some tag => exact ⟨valid, valid request tag found⟩
    | none => exact ⟨storage.put_consistent function state.1 valid request, rfl⟩

def associationList : Storage Input Tag where
  State := List (Input × Tag)
  empty := []
  lookup state request := state.lookup request
  put state request tag := (request, tag) :: state
  empty_lookup := by intro request; rfl
  put_same := by intro state request tag; simp
  put_other := by
    intro state request tag other different
    simp [List.lookup_cons, beq_eq_false_iff_ne.mpr different]

def indexedTable : Storage Input Tag where
  State := Input → Option Tag
  empty := fun _ => none
  lookup state request := state request
  put state request tag := Function.update state request (some tag)
  empty_lookup := by intro request; rfl
  put_same := by intro state request tag; simp
  put_other := by intro state request tag other different; simp [Function.update_of_ne different]

variable [DecidableEq Tag]

structure GameObservation (Input Tag : Type) where
  candidate : Input × Tag
  signingTranscript : List (Input × Tag)
  accepted : Bool
  cursor : Nat
  deriving DecidableEq

def finishObservation (past : Observation Input Tag (Input × Tag)) (answer : Tag) :
    GameObservation Input Tag :=
  ⟨past.result, past.transcript,
    decide (past.result.1 ∉ past.transcript.map Prod.fst) && decide (answer = past.result.2), past.cursor⟩

def referenceGame (function : Input → Tag) (coins : Nat → Bool)
    (attack : Program Input Tag (Input × Tag)) : GameObservation Input Tag :=
  let past := reference function coins 0 attack
  finishObservation past (function past.result.1)

/-- The private verification query is actually omitted on the rejecting branch.
The final state therefore need not be equal to a non-aborting execution state. -/
def game (model : Model Input Tag) (early : Bool) (function : Input → Tag) (coins : Nat → Bool)
    (attack : Program Input Tag (Input × Tag)) : GameObservation Input Tag × model.State :=
  let past := execute model function coins 0 model.initial attack
  if early && decide (past.observation.result.1 ∈ past.observation.transcript.map Prod.fst) then
    (⟨past.observation.result, past.observation.transcript, false, past.observation.cursor⟩, past.state)
  else
    let answer := model.step function past.state past.observation.result.1
    (finishObservation past.observation answer.2, answer.1)

/-- All whole-game public correspondence is derived, including true early
rejection and arbitrary response-dependent signing queries and local coins. -/
theorem game_correct (model : Model Input Tag) (early : Bool) (function : Input → Tag)
    (coins : Nat → Bool) (attack : Program Input Tag (Input × Tag)) :
    (game model early function coins attack).1 = referenceGame function coins attack := by
  obtain ⟨same, valid⟩ := execute_correct model function coins attack 0 model.initial
    (model.initial_valid function)
  have answer := (model.step_valid function
    (execute model function coins 0 model.initial attack).state
    (execute model function coins 0 model.initial attack).observation.result.1 valid).2
  unfold game
  dsimp only
  split
  · rename_i rejected
    have member : (execute model function coins 0 model.initial attack).observation.result.1 ∈
        (execute model function coins 0 model.initial attack).observation.transcript.map Prod.fst := by
      by_contra absent
      simp [absent] at rejected
    simp only [same] at member ⊢
    simp [referenceGame, finishObservation, member]
  · rw [answer, same]
    rfl

/-- No supplied family of whole-game correspondences is needed, even when the
private state types differ between vertices. -/
theorem family_correct {Index : Type} (models : Index → Model Input Tag) (early : Index → Bool)
    (function : Input → Tag) (coins : Nat → Bool) (attack : Program Input Tag (Input × Tag)) :
    (fun index => (game (models index) (early index) function coins attack).1) =
      (fun _ => referenceGame function coins attack) := by
  funext index
  exact game_correct _ _ _ _ _

abbrev World (Input Tag : Type) := (Input → Tag) × (Nat → Bool)

/-- The original function and coin tape are retained, not resampled per vertex.
The supplied world law has no claimed independent-lazy-sampling marginal. -/
noncomputable def joint {Index : Type} (law : PMF (World Input Tag))
    (models : Index → Model Input Tag) (early : Index → Bool)
    (attack : Program Input Tag (Input × Tag)) :=
  law.map fun world => (world, fun index => (game (models index) (early index) world.1 world.2 attack).1)

theorem joint_retains_world {Index : Type} (law : PMF (World Input Tag))
    (models : Index → Model Input Tag) (early : Index → Bool) (attack : Program Input Tag (Input × Tag)) :
    (joint law models early attack).map Prod.fst = law := by
  rw [joint, PMF.map_comp]
  change law.map id = law
  exact PMF.map_id law

theorem joint_vertex {Index : Type} (law : PMF (World Input Tag))
    (models : Index → Model Input Tag) (early : Index → Bool)
    (attack : Program Input Tag (Input × Tag)) (index : Index) :
    (joint law models early attack).map (fun pair => pair.2 index) =
      law.map (fun world => (game (models index) (early index) world.1 world.2 attack).1) := by
  simp only [joint, PMF.map_comp, Function.comp_def]

theorem joint_generated {Index : Type} (law : PMF (World Input Tag))
    (models : Index → Model Input Tag) (early : Index → Bool) (attack : Program Input Tag (Input × Tag)) :
    joint law models early attack =
      law.map (fun world => (world, fun _ : Index => referenceGame world.1 world.2 attack)) := by
  unfold joint
  congr 1
  funext world
  rw [family_correct]

/-- The selected overlapping attack: a repeated request after an adaptive one,
followed by both an already-signed and a fresh candidate branch. -/
def attack : Program (Fin 4) (Fin 256) (Fin 4 × Fin 256) :=
  .query 0 fun tag => .query (if tag.val % 2 = 0 then 1 else 2) fun _ =>
    .query 0 fun _ => .coin fun fresh => .done (if fresh then (3, tag) else (0, tag))

def configurations (config : Bool × Bool × Bool) : Model (Fin 4) (Fin 256) :=
  if config.1 then indexedTable.model config.2.1 else associationList.model config.2.1

theorem eight_configurations (function : Fin 4 → Fin 256) (coins : Nat → Bool) :
    (fun config : Bool × Bool × Bool =>
      (game (configurations config) config.2.2 function coins attack).1) =
      (fun _ => referenceGame function coins attack) :=
  family_correct configurations (fun config => config.2.2) function coins attack

/-- These count backend calls recorded by the replay interpreter. No native
machine execution or total execution-time bound is asserted here. -/
theorem reject_without_optimization_calls :
    (game (associationList.model false) false (fun _ : Fin 4 => (0 : Fin 256))
      (fun _ => false) attack).2.2.length = 4 := by decide

theorem reject_with_optimization_calls :
    (game (associationList.model true) true (fun _ : Fin 4 => (0 : Fin 256))
      (fun _ => false) attack).2.2.length = 2 := by decide

theorem fresh_with_optimization_calls :
    (game (associationList.model true) true (fun _ : Fin 4 => (0 : Fin 256))
      (fun _ => true) attack).2.2.length = 3 := by decide

end Foundation.Examples.RandomFunctionMACLocalRealization
