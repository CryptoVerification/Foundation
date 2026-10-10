import Foundation.Constructions.Hash.CoordinateTerminal

/-! Actual coordinate-real allocation invariants, including private hash
computations and adaptive public compression requests. The remaining supply is
fresh in the coordinate cache, and all cached values agree with the fixed
coordinate function. These are structural invariants, not collision exclusions
or a bound on machine time. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest]
  [DecidableEq Label] [Fintype Digest] [Nonempty Digest]

omit [DecidableEq Digest] in
/-- Each fixed-coordinate allocator transition is supported by the existing
lazy-coordinate allocator, retaining every backend component and the response.
The independent hash kernel is identical on both sides. -/
theorem real_coordinate_eager_step_support (function : Label → Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : RealCoordinateState Payload Digest Label) (request : SimulatorRequest Payload)
    (answer : RealCoordinateState Payload Digest Label × Digest)
    (support : answer ∈ (realCoordinateWorld (RandomOracle.eager function) hashOracle state request).support) :
    answer ∈ (realCoordinateWorld RandomOracle.oracle hashOracle state request).support := by
  unfold realCoordinateWorld Program.statefulOracle at support ⊢
  rw [PMF.mem_support_map_iff] at support ⊢
  obtain ⟨out, reachable, same⟩ := support
  have transferred := Program.run_support_state_map id
    (RandomOracle.withContext (simulatorBackend hashOracle) (RandomOracle.eager function))
    (RandomOracle.withContext (simulatorBackend hashOracle) RandomOracle.oracle)
    (by intro backend query response present
        simpa only [id_eq, Prod.mk.eta] using
          RandomOracle.eager_context_step_support function (simulatorBackend hashOracle)
            backend query response present)
    (realCoordinateProgram state.1 request) state.2 out reachable
  exact ⟨out, by simpa only [Program.mapState, id_eq] using transferred, same⟩

omit [DecidableEq Digest] in
/-- Fresh remaining labels and fixed-coordinate cache values are preserved by
one actual allocator transition. The coordinate function need not be injective. -/
theorem real_coordinate_eager_step_invariants (function : Label → Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : RealCoordinateState Payload Digest Label)
    (valid : RealCoordinateValid state ∧ RandomOracle.TableValues function state.2.2)
    (request : SimulatorRequest Payload) (answer : RealCoordinateState Payload Digest Label × Digest)
    (support : answer ∈ (realCoordinateWorld (RandomOracle.eager function) hashOracle state request).support) :
    RealCoordinateValid answer.1 ∧ RandomOracle.TableValues function answer.1.2.2 := by
  refine ⟨realCoordinate_step_valid state valid.1 request answer
    (real_coordinate_eager_step_support function hashOracle state request answer support), ?_⟩
  unfold realCoordinateWorld Program.statefulOracle at support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨out, reachable, rfl⟩ := support
  exact RandomOracle.eager_context_run_values function (simulatorBackend hashOracle)
    (realCoordinateProgram state.1 request) state.2.1 state.2.2 valid.2 out reachable

/-- Internal full-table compression calls preserve allocator freshness and
fixed-coordinate cache values, including recognized terminal hash calls. -/
theorem coordinate_compression_allocation_invariants (initial : Digest) (terminal : Payload)
    (function : Label → Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : CoordinateRealState Payload Digest Label)
    (valid : RealCoordinateValid state.2 ∧ RandomOracle.TableValues function state.2.2.2)
    (input : CompressionInput Payload Digest) (answer : CoordinateRealState Payload Digest Label × Digest)
    (support : answer ∈ (Program.statefulOracle (simulatorProgram initial terminal)
      (realCoordinateWorld (RandomOracle.eager function) hashOracle) state input).support) :
    RealCoordinateValid answer.1.2 ∧ RandomOracle.TableValues function answer.1.2.2.2 := by
  unfold Program.statefulOracle at support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨out, reachable, rfl⟩ := support
  exact Program.run_preserves _
    (fun backend => RealCoordinateValid backend ∧ RandomOracle.TableValues function backend.2.2)
    (real_coordinate_eager_step_invariants function hashOracle)
    (simulatorProgram initial terminal state.1 input) state.2 valid out reachable

/-- One actual outer call includes the whole high-level hash computation,
not just the publicly visible compression branch. -/
theorem coordinate_real_step_allocation_invariants (initial : Digest) (terminal : Payload)
    (function : Label → Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : CoordinateRealState Payload Digest Label)
    (valid : RealCoordinateValid state.2 ∧ RandomOracle.TableValues function state.2.2.2)
    (request : WorldInput Payload Digest) (answer : CoordinateRealState Payload Digest Label × Digest)
    (support : answer ∈ (coordinateRealWorld initial terminal (RandomOracle.eager function)
      hashOracle state request).support) :
    RealCoordinateValid answer.1.2 ∧ RandomOracle.TableValues function answer.1.2.2.2 := by
  unfold coordinateRealWorld Program.implementedOracle at support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨out, reachable, rfl⟩ := support
  exact Program.run_preserves _
    (fun pair => RealCoordinateValid pair.2 ∧ RandomOracle.TableValues function pair.2.2.2)
    (coordinate_compression_allocation_invariants initial terminal function hashOracle)
    (compressionCall initial terminal request) state valid out reachable

/-- Both allocation invariants hold through arbitrary adaptive complete
outer executions with an arbitrary independent hash kernel. -/
theorem coordinate_real_run_allocation_invariants {Result : Type}
    (initial : Digest) (terminal : Payload) (function : Label → Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : CoordinateRealState Payload Digest Label)
    (valid : RealCoordinateValid state.2 ∧ RandomOracle.TableValues function state.2.2.2)
    (out : Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label))
    (support : out ∈ (attack.run (coordinateRealWorld initial terminal (RandomOracle.eager function)
      hashOracle) state).support) :
    RealCoordinateValid out.state.2 ∧ RandomOracle.TableValues function out.state.2.2.2 :=
  Program.run_preserves _
    (fun pair => RealCoordinateValid pair.2 ∧ RandomOracle.TableValues function pair.2.2.2)
    (coordinate_real_step_allocation_invariants initial terminal function hashOracle)
    attack state valid out support

/-- Starting with a duplicate-free supply and an empty coordinate cache,
all remaining labels are fresh and all allocated values agree with the chosen
function. The initial full compression and hash tables are arbitrary. -/
theorem coordinate_real_allocation_from_empty {Result : Type}
    (initial : Digest) (terminal : Payload) (function : Label → Digest)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (supply : List Label) (nodup : supply.Nodup) (flag : Bool)
    (full : CompressionTable Payload Digest) (hashes : RandomOracle.Table (List Payload) Digest)
    (out : Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label))
    (support : out ∈ (attack.run (coordinateRealWorld initial terminal (RandomOracle.eager function)
      hashOracle) (full, ((supply, flag), (hashes, [])))).support) :
    RealCoordinateValid out.state.2 ∧ RandomOracle.TableValues function out.state.2.2.2 :=
  coordinate_real_run_allocation_invariants initial terminal function hashOracle attack
    (full, ((supply, flag), (hashes, [])))
    ⟨⟨nodup, by intro label member; rfl⟩, by intro entry member; cases member⟩ out support

end Foundation.Hash
