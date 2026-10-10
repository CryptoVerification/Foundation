import Foundation.Constructions.Hash.Expansion
import Foundation.Crypto.Semantics.Oracle.QuerySecurity

/-! Strong simulator quantification over a two-interface Foundation protocol.
A simulator procedure receives only private state and low-level requests. Its
only access to the ideal hash is a syntactic oracle call. Local uniform draws
use a separate internal window and share no hidden hash state with the procedure.

QueryIndifferentiable is the query-semantics part of indifferentiability. It does
not assert a machine-time or storage bound for the simulator. The quantitative
candidate theorem is proved in QueryIndifferentiability.lean.
-/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
open scoped ENNReal

structure Simulator (Payload Digest : Type) where
  PrivateState : Type
  initial : PrivateState
  procedure : PrivateState → CompressionInput Payload Digest →
    Program (SimulatorRequest Payload) Digest (PrivateState × Digest)

variable {Payload Digest : Type} [DecidableEq Payload] [DecidableEq Digest]
  [Fintype Digest] [Nonempty Digest]

noncomputable def Simulator.world (S : Simulator Payload Digest)
    {IdealState : Type} (ideal : Oracle (List Payload) Digest IdealState) :
    Oracle (WorldInput Payload Digest) Digest (S.PrivateState × IdealState) :=
  fun (privateState, state) request => match request with
    | .inl message => (ideal state message).map (fun answer => ((privateState, answer.1), answer.2))
    | .inr input => Program.statefulOracle S.procedure (simulatorBackend ideal)
        (privateState, state) input

/-- A bound on internal calls; local random draws and ideal-hash queries can
be counted separately by inspecting the two internal request constructors. -/
def Simulator.CallsBound (S : Simulator Payload Digest) (calls : Nat) : Prop :=
  ∀ state input, (S.procedure state input).BoundedQueries calls

def candidate (initial : Digest) (terminal : Payload) : Simulator Payload Digest where
  PrivateState := CompressionTable Payload Digest
  initial := []
  procedure := simulatorProgram initial terminal

omit [Fintype Digest] [Nonempty Digest] in
theorem candidate_calls (initial : Digest) (terminal : Payload) :
    (candidate initial terminal).CallsBound 1 :=
  simulatorProgram_queries initial terminal

theorem candidate_world (initial : Digest) (terminal : Payload)
    {IdealState : Type} (ideal : Oracle (List Payload) Digest IdealState) :
    (candidate initial terminal).world ideal = idealWorld ideal initial terminal := rfl

/-- Left and right hidden states are different types; the ordinary Foundation
security goal executes exactly the same adversary syntax in both worlds. -/
noncomputable def protocol (S : Simulator Payload Digest) (initial : Digest) (terminal : Payload) :
    Protocol (WorldInput Payload Digest) Digest (CompressionTable Payload Digest)
      (S.PrivateState × RandomOracle.Table (List Payload) Digest) where
  Instance := fun _ => Unit
  games _ _ :=
    { left := realWorld initial terminal
      right := S.world RandomOracle.oracle
      leftInitial := []
      rightInitial := (S.initial, []) }

/-- One simulator is chosen before all distinguishers, as in the strong CDMP
quantifier order. The per-message bound counts encoded compression blocks.
The simulator's internal-call bound is independent of the distinguisher. -/
def QueryIndifferentiable (initial : Digest) (terminal : Payload)
    (blockLimit queries simulatorCalls : Nat) (error : ℝ≥0∞) : Prop :=
  ∃ S : Simulator Payload Digest, S.CallsBound simulatorCalls ∧
    ∀ attack : Program (WorldInput Payload Digest) Digest Bool,
      WorldBound blockLimit attack queries →
      (CryptoOracle.goal (protocol S initial terminal)).advantage 0 () attack ≤ error

/-- The existing zero-query security theorem also applies to heterogeneous
hidden states. This is only a sanity check; it is not the hash security result. -/
theorem zero_query_advantage (S : Simulator Payload Digest) (initial : Digest)
    (terminal : Payload) (attack : Program (WorldInput Payload Digest) Digest Bool)
    (bound : attack.BoundedQueries 0) :
    (CryptoOracle.goal (protocol S initial terminal)).advantage 0 () attack = 0 := by
  change probabilityGap _ _ = 0
  rw [bound.zero_run_result_eq
    ((protocol S initial terminal).games 0 ()).left
    ((protocol S initial terminal).games 0 ()).right
    ((protocol S initial terminal).games 0 ()).leftInitial
    ((protocol S initial terminal).games 0 ()).rightInitial]
  simp [probabilityGap]

end Foundation.Hash
