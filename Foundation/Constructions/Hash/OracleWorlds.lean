import Foundation.Constructions.Hash.PrefixFree
import Foundation.Crypto.Semantics.Oracle.RandomOracle
import Foundation.Crypto.Semantics.Oracle.Composition

/-! Two interfaces for prefix-free Merkle–Damgård.
The real hash shares the compression table with the public compression interface.
The simulator only receives an ideal-oracle operation; its control flow cannot
inspect the ideal state or the distinguisher's high-level query history.

The simulator follows predecessor data edges to reconstruct a complete message.
It is a candidate for the strong indifferentiability proof, not a security theorem.
Collisions and hidden-chain guesses still require a coupling and probability bound.
The marker-terminal encoding specializes the complete-chain strategy of CDMP
(Appendix A.2) and Backes et al. (CSF 2012, Section V). No external code is copied.
-/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability

variable {Payload Digest IdealState : Type}
  [DecidableEq Payload] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest]

abbrev CompressionInput (Payload Digest : Type) := Digest × (Bool × Payload)
abbrev CompressionTable (Payload Digest : Type) :=
  RandomOracle.Table (CompressionInput Payload Digest) Digest
abbrev WorldInput (Payload Digest : Type) :=
  List Payload ⊕ CompressionInput Payload Digest

/-- Only data edges can occur before the unique terminal block. -/
def dataEdges (table : CompressionTable Payload Digest) :
    List (Digest × (Digest × Payload)) :=
  table.filterMap fun entry =>
    if entry.1.2.1 then none else some (entry.2, (entry.1.1, entry.1.2.2))

/-- Search backwards using at most `fuel` table edges. At collisions the first
predecessor is selected; uniqueness will be required only outside the bad event. -/
def messagePrefix (initial : Digest) (table : CompressionTable Payload Digest) :
    Nat → Digest → Option (List Payload)
  | 0, target => if target = initial then some [] else none
  | fuel + 1, target =>
      if target = initial then some [] else
        match (dataEdges table).lookup target with
        | none => none
        | some (previous, block) =>
            (messagePrefix initial table fuel previous).map (fun blocks => blocks ++ [block])

/-- Real high-level evaluation executes all compression calls with the same
state as the low-level interface. Internal compression traces are not public. -/
noncomputable def realWorld (initial : Digest) (terminal : Payload) :
    Oracle (WorldInput Payload Digest) Digest (CompressionTable Payload Digest) :=
  fun table request => match request with
    | .inl message =>
        ((prefixFreeMD initial terminal message).run RandomOracle.oracle table).map
          (fun outcome => (outcome.state, outcome.result))
    | .inr input => RandomOracle.oracle table input

/-- The internal left window accesses the ideal hash. The right window draws
local uniform randomness and does not count as an ideal-hash query. -/
abbrev SimulatorRequest (Payload : Type) := List Payload ⊕ Unit

/-- Recover the message associated with a well-marked terminal input using
only the private/public compression table, never the shared ideal-hash state. -/
def terminalMessage (initial : Digest) (terminal : Payload)
    (table : CompressionTable Payload Digest) (input : CompressionInput Payload Digest) :
    Option (List Payload) :=
  if input.2.1 = true ∧ input.2.2 = terminal then
    messagePrefix initial table table.length input.1
  else none

/-- The procedure can inspect only the private compression table. The ideal
oracle's state and the distinguisher's high-level transcript are absent here. -/
def simulatorProgram (initial : Digest) (terminal : Payload)
    (table : CompressionTable Payload Digest) (input : CompressionInput Payload Digest) :
    Program (SimulatorRequest Payload) Digest (CompressionTable Payload Digest × Digest) :=
  match table.lookup input with
  | some output => .done (table, output)
  | none =>
    let remember := fun output => Program.done ((input, output) :: table, output)
    match terminalMessage initial terminal table input with
    | some message => .query (.inl message) remember
    | none => .query (.inr ()) remember

/-- This interpreter owns the ideal state. A local random draw preserves it. -/
noncomputable def simulatorBackend (ideal : Oracle (List Payload) Digest IdealState) :
    Oracle (SimulatorRequest Payload) Digest IdealState :=
  fun state request => match request with
    | .inl message => ideal state message
    | .inr () => (uniform Digest).map (fun output => (state, output))

noncomputable def compressionSimulator
    (ideal : Oracle (List Payload) Digest IdealState)
    (initial : Digest) (terminal : Payload) :
    Oracle (CompressionInput Payload Digest) Digest
      (CompressionTable Payload Digest × IdealState) :=
  Program.statefulOracle (simulatorProgram initial terminal) (simulatorBackend ideal)

/-- The execution equation is proved from the procedure's interpreter; it is
not a second implementation or an assumed semantic realization. -/
theorem compressionSimulator_eq
    (ideal : Oracle (List Payload) Digest IdealState)
    (initial : Digest) (terminal : Payload)
    (table : CompressionTable Payload Digest) (state : IdealState)
    (input : CompressionInput Payload Digest) :
    compressionSimulator ideal initial terminal (table, state) input =
      match table.lookup input with
    | some output => PMF.pure ((table, state), output)
    | none =>
      let remember := fun (answer : IdealState × Digest) =>
        (((input, answer.2) :: table, answer.1), answer.2)
      if input.2.1 = true ∧ input.2.2 = terminal then
        match messagePrefix initial table table.length input.1 with
        | some message => (ideal state message).map remember
        | none => (uniform Digest).map (fun output => remember (state, output))
      else (uniform Digest).map (fun output => remember (state, output)) := by
  cases ht : table.lookup input with
  | some output =>
      simp [compressionSimulator, Program.statefulOracle, simulatorProgram, ht,
        Program.run, PMF.pure_map]
  | none =>
      by_cases hc : input.2.1 = true ∧ input.2.2 = terminal
      · cases hp : messagePrefix initial table table.length input.1 with
        | none =>
            simp [compressionSimulator, Program.statefulOracle, simulatorProgram, terminalMessage,
              simulatorBackend, ht, hc, hp, Program.run, PMF.pure_map, PMF.map_bind,
              Function.comp_def]
            rfl
        | some message =>
            simp [compressionSimulator, Program.statefulOracle, simulatorProgram, terminalMessage,
              simulatorBackend, ht, hc, hp, Program.run, PMF.pure_map, PMF.map_bind]
            rfl
      · simp [compressionSimulator, Program.statefulOracle, simulatorProgram, terminalMessage,
          simulatorBackend, ht, hc, Program.run, PMF.pure_map, PMF.map_bind,
          Function.comp_def]
        rfl

/-- The recognizer form of the execution equation keeps all callers on the
same terminal-message search procedure. -/
theorem compressionSimulator_terminal_eq
    (ideal : Oracle (List Payload) Digest IdealState)
    (initial : Digest) (terminal : Payload)
    (table : CompressionTable Payload Digest) (state : IdealState)
    (input : CompressionInput Payload Digest) :
    compressionSimulator ideal initial terminal (table, state) input =
      match table.lookup input with
      | some output => PMF.pure ((table, state), output)
      | none => match terminalMessage initial terminal table input with
        | some message => (ideal state message).map (fun answer =>
            (((input, answer.2) :: table, answer.1), answer.2))
        | none => (uniform Digest).map (fun output =>
            (((input, output) :: table, state), output)) := by
  rw [compressionSimulator_eq]
  cases cached : table.lookup input with
  | some output => simp
  | none =>
      by_cases marked : input.2.1 = true ∧ input.2.2 = terminal
      · simp [terminalMessage, marked]
      · simp [terminalMessage, marked]

omit [Fintype Digest] [Nonempty Digest] in
/-- One internal call at most: either an ideal-hash query or a local draw.
This bound does not conflate the two kinds of calls. -/
theorem simulatorProgram_queries (initial : Digest) (terminal : Payload)
    (table : CompressionTable Payload Digest) (input : CompressionInput Payload Digest) :
    (simulatorProgram initial terminal table input).BoundedQueries 1 := by
  unfold simulatorProgram
  split
  · exact .done _ 1
  · split <;> exact .query _ _ 0 (fun output => .done _ 0)

/-- High-level queries go directly to the ideal oracle. The simulator's own
compression table is unchanged and the simulator receives no high-level log. -/
noncomputable def idealWorld
    (ideal : Oracle (List Payload) Digest IdealState)
    (initial : Digest) (terminal : Payload) :
    Oracle (WorldInput Payload Digest) Digest
      (CompressionTable Payload Digest × IdealState) :=
  fun (table, state) request => match request with
    | .inl message => (ideal state message).map (fun answer => ((table, answer.1), answer.2))
    | .inr input => compressionSimulator ideal initial terminal (table, state) input

theorem simulator_known (ideal : Oracle (List Payload) Digest IdealState)
    (initial : Digest) (terminal : Payload) (table : CompressionTable Payload Digest)
    (state : IdealState) (input : CompressionInput Payload Digest) (output : Digest)
    (h : table.lookup input = some output) :
    compressionSimulator ideal initial terminal (table, state) input =
      PMF.pure ((table, state), output) := by
  rw [compressionSimulator_eq]
  simp [h]

/-- Each simulator call either preserves its private table or records exactly
one new compression input and its returned output. -/
theorem simulator_step (ideal : Oracle (List Payload) Digest IdealState)
    (initial : Digest) (terminal : Payload) (table : CompressionTable Payload Digest)
    (state : IdealState) (input : CompressionInput Payload Digest)
    (answer : (CompressionTable Payload Digest × IdealState) × Digest)
    (h : answer ∈ (compressionSimulator ideal initial terminal (table, state) input).support) :
    answer.1.1 = table ∨ answer.1.1 = (input, answer.2) :: table := by
  rw [compressionSimulator_eq] at h
  split at h
  · simp only [PMF.mem_support_pure_iff] at h
    subst answer
    exact Or.inl rfl
  · have hm {Answer : Type} (p : ProbComp Answer) (f : Answer → IdealState × Digest)
        (hs : answer ∈ (p.map (fun a =>
          (((input, (f a).2) :: table, (f a).1), (f a).2))).support) :
        answer.1.1 = (input, answer.2) :: table := by
      rw [PMF.mem_support_map_iff] at hs
      obtain ⟨a, _, he⟩ := hs
      subst answer
      rfl
    right
    split at h
    · split at h
      · exact hm _ id h
      · exact hm _ (fun output => (state, output)) h
    · exact hm _ (fun output => (state, output)) h

theorem simulator_table_length (ideal : Oracle (List Payload) Digest IdealState)
    (initial : Digest) (terminal : Payload) (table : CompressionTable Payload Digest)
    (state : IdealState) (input : CompressionInput Payload Digest)
    (answer : (CompressionTable Payload Digest × IdealState) × Digest)
    (h : answer ∈ (compressionSimulator ideal initial terminal (table, state) input).support) :
    answer.1.1.length ≤ table.length + 1 := by
  rcases simulator_step ideal initial terminal table state input answer h with he | he
  · simp [he]
  · simp [he]

/-- Servicing a high-level query never modifies the simulator's private table. -/
theorem ideal_high_private_table (ideal : Oracle (List Payload) Digest IdealState)
    (initial : Digest) (terminal : Payload) (table : CompressionTable Payload Digest)
    (state : IdealState) (message : List Payload) :
    (idealWorld ideal initial terminal (table, state) (.inl message)).map
      (fun answer => answer.1.1) = PMF.pure table := by
  simp only [idealWorld, PMF.map_comp, Function.comp_def]
  change ((ideal state message).bind (fun _ => PMF.pure table)) = PMF.pure table
  simp

end Foundation.Hash
