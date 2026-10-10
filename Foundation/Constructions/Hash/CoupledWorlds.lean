import Foundation.Constructions.Hash.FiniteHashWorld
import Foundation.Constructions.Hash.LatentLiterals
import Foundation.Constructions.Hash.LatentPublicTerminal
import Foundation.Constructions.Hash.CoordinateTerminal
import Foundation.Constructions.Hash.CoordinateAllocation
import Foundation.Constructions.Hash.LatentPairedStep
import Foundation.Constructions.Hash.LatentStructure
import Foundation.Constructions.Hash.CoordinateInvariant
import Foundation.Crypto.Semantics.Oracle.CoupledRun
import Foundation.Crypto.Semantics.Oracle.RandomOracleFiniteCollision

/-! A concrete common probability space for the actual real and fixed-candidate
ideal experiments. Both finite functions and attacker coins are shared; each
whole final-state marginal is proved. The agreement and quantitative security proof using this common space are
provided in CoordinateAgreement.lean and QueryIndifferentiability.lean. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
variable {Payload Digest Label Result : Type} [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label]
  [Fintype Digest] [Nonempty Digest] [Fintype Label]

/-- The hidden coordinate function and finite hash function are sampled once.
The original two-window interfaces are run directly, with shared attacker coins
until responses differ. Neither hidden function is given to the simulator. The existing proof-only
monitor retains an earlier hidden-coordinate guess even after later disclosure. -/
noncomputable def coupledCoordinateWorlds (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result) (fallback : Digest) :
    PMF ((Label → Digest) ×
      (({message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest) ×
      (Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label) ×
       Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label × Bool)))) :=
  (uniform (Label → Digest)).bind fun coordinates =>
    (uniform ({message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest)).bind fun hashes =>
      (Program.coupledRun
        (coordinateRealWorld initial terminal (RandomOracle.eager coordinates)
          (RandomOracle.eager (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback hashes)))
        (Program.monitorOracle (latentGuessHit coordinates)
          (latentCoordinateWorld initial terminal (RandomOracle.eager coordinates)
            (RandomOracle.eager (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback hashes))))
        ([], ((supply, false), ([], []))) ((LatentState.empty supply, ([], [])), false) attack).map
          (fun pair => (coordinates, (hashes, pair)))

/-- Every supported joint entry provides actual supported outer runs on
both sides with the same sampled functions. This is support transport from the
exact marginals, retaining the monitor flag and complete outer transcripts. -/
theorem coupled_coordinate_support (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result) (fallback : Digest)
    (entry : (Label → Digest) ×
      (({message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest) ×
      (Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label) ×
       Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label × Bool))))
    (support : entry ∈ (coupledCoordinateWorlds initial terminal supply attack fallback).support) :
    entry.2.2.1 ∈ (attack.run (coordinateRealWorld initial terminal (RandomOracle.eager entry.1)
      (RandomOracle.eager (RandomOracle.extendFinite
        (coordinateHashDomain initial terminal supply attack) fallback entry.2.1)))
      ([], ((supply, false), ([], [])))).support ∧
    entry.2.2.2 ∈ (attack.run (Program.monitorOracle (latentGuessHit entry.1)
      (latentCoordinateWorld initial terminal (RandomOracle.eager entry.1)
        (RandomOracle.eager (RandomOracle.extendFinite
          (coordinateHashDomain initial terminal supply attack) fallback entry.2.1))))
      ((LatentState.empty supply, ([], [])), false)).support := by
  unfold coupledCoordinateWorlds at support
  rw [PMF.mem_support_bind_iff] at support
  obtain ⟨coordinates, _, support⟩ := support
  rw [PMF.mem_support_bind_iff] at support
  obtain ⟨hashes, _, support⟩ := support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨pair, reachable, rfl⟩ := support
  have marginals := Program.coupledRun_marginals
    (coordinateRealWorld initial terminal (RandomOracle.eager coordinates)
      (RandomOracle.eager (RandomOracle.extendFinite
        (coordinateHashDomain initial terminal supply attack) fallback hashes)))
    (Program.monitorOracle (latentGuessHit coordinates)
      (latentCoordinateWorld initial terminal (RandomOracle.eager coordinates)
        (RandomOracle.eager (RandomOracle.extendFinite
          (coordinateHashDomain initial terminal supply attack) fallback hashes))))
    attack ([], ((supply, false), ([], []))) ((LatentState.empty supply, ([], [])), false)
  constructor
  · rw [← marginals.1, PMF.mem_support_map_iff]
    exact ⟨pair, reachable, rfl⟩
  · rw [← marginals.2, PMF.mem_support_map_iff]
    exact ⟨pair, reachable, rfl⟩

/-- The left whole-state/result marginal is exactly the existing finite
coordinate real experiment. No no-collision or capacity premise is needed. -/
theorem coupled_coordinate_real_marginal (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result) (fallback : Digest) :
    (coupledCoordinateWorlds initial terminal supply attack fallback).map
      (fun entry => Program.resultState entry.2.2.1) =
    (uniform (Label → Digest)).bind (fun coordinates =>
      (attack.run (coordinateRealWorld initial terminal (RandomOracle.eager coordinates))
        ([], ((supply, false), ([], [])))).map Program.resultState) := by
  unfold coupledCoordinateWorlds
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  congr 1
  funext coordinates
  have marginal (hashes : {message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest) :=
    congrArg (PMF.map Program.resultState) (Program.coupledRun_marginals
      (coordinateRealWorld initial terminal (RandomOracle.eager coordinates)
        (RandomOracle.eager (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback hashes)))
      (Program.monitorOracle (latentGuessHit coordinates)
        (latentCoordinateWorld initial terminal (RandomOracle.eager coordinates)
          (RandomOracle.eager (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback hashes))))
      attack ([], ((supply, false), ([], []))) ((LatentState.empty supply, ([], [])), false)).1
  simp only [PMF.map_comp, Function.comp_def] at marginal
  simp_rw [marginal]
  exact finite_total_real_execution initial terminal supply attack (RandomOracle.eager coordinates) fallback

/-- The right whole-state/result marginal is exactly the existing finite
coordinate ideal experiment, including the controller's full symbolic graph. -/
theorem coupled_coordinate_ideal_marginal (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result) (fallback : Digest) :
    (coupledCoordinateWorlds initial terminal supply attack fallback).map
      (fun entry => (entry.2.2.2.state.1, entry.2.2.2.result)) =
    (uniform (Label → Digest)).bind (fun coordinates =>
      (attack.run (latentCoordinateWorld initial terminal (RandomOracle.eager coordinates))
        (LatentState.empty supply, ([], []))).map Program.resultState) := by
  unfold coupledCoordinateWorlds
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  congr 1
  funext coordinates
  have marginal (hashes : {message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest) :=
    congrArg (PMF.map (fun out => (out.state.1, out.result))) (Program.coupledRun_marginals
      (coordinateRealWorld initial terminal (RandomOracle.eager coordinates)
        (RandomOracle.eager (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback hashes)))
      (Program.monitorOracle (latentGuessHit coordinates)
        (latentCoordinateWorld initial terminal (RandomOracle.eager coordinates)
          (RandomOracle.eager (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback hashes))))
      attack ([], ((supply, false), ([], []))) ((LatentState.empty supply, ([], [])), false)).2
  have erased (hashes : {message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest) :=
    congrArg (PMF.map Program.resultState) (Program.monitor_run_erase (latentGuessHit coordinates)
      (latentCoordinateWorld initial terminal (RandomOracle.eager coordinates)
        (RandomOracle.eager (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback hashes)))
      attack (LatentState.empty supply, ([], [])) false)
  simp only [PMF.map_comp, Program.resultState, Program.mapState, Function.comp_def] at marginal erased
  have combined (hashes : {message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest) :=
    (marginal hashes).trans (erased hashes)
  simp_rw [combined]
  exact finite_total_ideal_execution initial terminal supply attack (RandomOracle.eager coordinates) fallback

/-- Projecting the real private compression table and result gives the actual
real experiment's joint law, using only a distinct initial label supply. -/
theorem coupled_real_marginal (initial : Digest) (terminal : Payload) (supply : List Label)
    (nodup : supply.Nodup) (attack : Program (WorldInput Payload Digest) Digest Result) (fallback : Digest) :
    (coupledCoordinateWorlds initial terminal supply attack fallback).map
      (fun entry => (entry.2.2.1.state.1, entry.2.2.1.result)) =
      (attack.run (realWorld initial terminal) []).map Program.resultState := by
  have same := congrArg (PMF.map (fun pair => (pair.1.1, pair.2)))
    (coupled_coordinate_real_marginal initial terminal supply attack fallback)
  simp only [PMF.map_bind, PMF.map_comp, Program.resultState, Function.comp_def] at same
  exact same.trans (coordinate_real_eager_marginal initial terminal supply nodup attack)

/-- The ideal public final state and result give the actual single fixed
candidate simulator's law. The simulator does not depend on the attacker. -/
theorem coupled_ideal_marginal (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result) (fallback : Digest) :
    (coupledCoordinateWorlds initial terminal supply attack fallback).map
      (fun entry => (latentView entry.2.2.2.state.1, entry.2.2.2.result)) =
      (attack.run ((candidate initial terminal).world RandomOracle.oracle) ([], [])).map Program.resultState := by
  have lazySame := (coupled_coordinate_ideal_marginal initial terminal supply attack fallback).trans
    (latent_eager_run initial terminal supply attack)
  have publicSame := congrArg (PMF.map (fun pair => (latentView pair.1, pair.2))) lazySame
  have candidateSame := congrArg (PMF.map Program.resultState)
    (latent_candidate_run initial terminal supply attack)
  simp only [PMF.map_comp, Program.resultState, Program.mapState, Function.comp_def] at publicSame candidateSame
  exact publicSame.trans candidateSame

/-- Shared coins ensure result agreement whenever the two public transcripts
agree. This is proved on the concrete joint law, including divergent runs. -/
theorem coupled_world_result_eq (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result) (fallback : Digest)
    (entry : (Label → Digest) ×
      (({message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest) ×
      (Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label) ×
       Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label × Bool))))
    (support : entry ∈ (coupledCoordinateWorlds initial terminal supply attack fallback).support)
    (traces : entry.2.2.1.trace = entry.2.2.2.trace) : entry.2.2.1.result = entry.2.2.2.result := by
  unfold coupledCoordinateWorlds at support
  rw [PMF.mem_support_bind_iff] at support
  obtain ⟨coordinates, _, support⟩ := support
  rw [PMF.mem_support_bind_iff] at support
  obtain ⟨hashes, _, support⟩ := support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨pair, reachable, rfl⟩ := support
  exact Program.coupledRun_result_eq_of_trace_eq _ _ attack _ _ pair reachable traces

/-- For any final-result event, the actual distinguishing gap is bounded by
public transcript disagreement in the explicit common law. The quantitative
bound is supplied separately in QueryIndifferentiability.lean. -/
theorem coupled_hash_gap_le (initial : Digest) (terminal : Payload) (supply : List Label)
    (nodup : supply.Nodup) (attack : Program (WorldInput Payload Digest) Digest Result)
    (fallback : Digest) (event : Result → Prop) :
    probabilityGap
      (eventProb (attack.run (realWorld initial terminal) []) (fun out => event out.result))
      (eventProb (attack.run ((candidate initial terminal).world RandomOracle.oracle) ([], []))
        (fun out => event out.result)) ≤
      eventProb (coupledCoordinateWorlds initial terminal supply attack fallback)
        (fun entry => entry.2.2.1.trace ≠ entry.2.2.2.trace) := by
  have gap := coupled_map_gap_le
    (coupledCoordinateWorlds initial terminal supply attack fallback)
    ((attack.run (realWorld initial terminal) []).map Program.resultState)
    ((attack.run ((candidate initial terminal).world RandomOracle.oracle) ([], [])).map Program.resultState)
    (fun entry => (entry.2.2.1.state.1, entry.2.2.1.result))
    (fun entry => (latentView entry.2.2.2.state.1, entry.2.2.2.result))
    (coupled_real_marginal initial terminal supply nodup attack fallback)
    (coupled_ideal_marginal initial terminal supply attack fallback)
    (fun pair => event pair.2) (fun pair => event pair.2)
    (fun entry => entry.2.2.1.trace ≠ entry.2.2.2.trace)
    (by intro entry reachable good
        have same := coupled_world_result_eq initial terminal supply attack fallback entry reachable
          (not_not.mp good)
        simp only [same])
  simpa only [eventProb_map, Program.resultState] using gap

/-- The historical hidden-guess flag has its concrete bound in this actual
joint law. Sampling order can be exchanged because the finite hash domain does
not depend on the coordinate function. No real/ideal state relation is assumed. -/
theorem coupled_online_guess_bound (initial : Digest) (terminal : Payload) (supply : List Label)
    {attack : Program (WorldInput Payload Digest) Digest Result} {q : Nat}
    (bound : attack.BoundedQueries q) (fallback : Digest) :
    eventProb (coupledCoordinateWorlds initial terminal supply attack fallback)
      (fun entry => entry.2.2.2.state.2 = true) ≤
      ((q * Fintype.card Label : Nat) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have law : (coupledCoordinateWorlds initial terminal supply attack fallback).map
      (fun entry => entry.2.2.2.state.2) =
      (uniform (Label → Digest)).bind (fun coordinates =>
        (uniform ({message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest)).bind
          (fun hashes => (attack.run (Program.monitorOracle (latentGuessHit coordinates)
            (latentCoordinateWorld initial terminal (RandomOracle.eager coordinates)
              (RandomOracle.eager (RandomOracle.extendFinite
                (coordinateHashDomain initial terminal supply attack) fallback hashes))))
            ((LatentState.empty supply, ([], [])), false)).map (fun out => out.state.2))) := by
    unfold coupledCoordinateWorlds
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    congr 1
    funext coordinates
    congr 1
    funext hashes
    have marginal := congrArg (PMF.map (fun out => out.state.2)) (Program.coupledRun_marginals
      (coordinateRealWorld initial terminal (RandomOracle.eager coordinates)
        (RandomOracle.eager (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback hashes)))
      (Program.monitorOracle (latentGuessHit coordinates)
        (latentCoordinateWorld initial terminal (RandomOracle.eager coordinates)
          (RandomOracle.eager (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback hashes))))
      attack ([], ((supply, false), ([], []))) ((LatentState.empty supply, ([], [])), false)).2
    simpa only [PMF.map_comp, Function.comp_def] using marginal
  have projected : eventProb ((coupledCoordinateWorlds initial terminal supply attack fallback).map
      (fun entry => entry.2.2.2.state.2)) (· = true) ≤
      ((q * Fintype.card Label : Nat) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
    rw [law, PMF.bind_comm]
    apply eventProb_bind_le
    intro hashes
    exact latent_online_guess_bound initial terminal supply bound
      (RandomOracle.eager (RandomOracle.extendFinite
        (coordinateHashDomain initial terminal supply attack) fallback hashes))
  simpa only [eventProb_map] using projected

/-- The chronological real-table failure bound transfers through the proved
real marginal of the concrete coupling, without a probability argument based
only on support. Internal compression calls are charged to q*blockLimit. -/
theorem coupled_forward_failure_bound {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) (supply : List Label) (nodup : supply.Nodup) (fallback : Digest) :
    eventProb (coupledCoordinateWorlds initial terminal supply attack fallback)
      (fun entry => ¬ForwardFresh initial entry.2.2.1.state.1) ≤
      ((2 * (q * blockLimit) * (q * blockLimit + 1) : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have same := congrArg (fun law => eventProb law (fun pair => ¬ForwardFresh initial pair.1))
    (coupled_real_marginal initial terminal supply nodup attack fallback)
  simp only [eventProb_map, Program.resultState] at same
  rw [same]
  exact real_forward_failure_bound bound initial terminal

/-- Two concrete failure events are bounded on one actual probability space.
This is not yet the transcript-disagreement bound: preservation of the full
paired state relation outside these and any remaining failures is still needed. -/
theorem coupled_forward_or_guess_bound {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) (supply : List Label) (nodup : supply.Nodup) (fallback : Digest) :
    eventProb (coupledCoordinateWorlds initial terminal supply attack fallback)
      (fun entry => ¬ForwardFresh initial entry.2.2.1.state.1 ∨ entry.2.2.2.state.2 = true) ≤
      ((2 * (q * blockLimit) * (q * blockLimit + 1) + q * Fintype.card Label : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ eventProb (coupledCoordinateWorlds initial terminal supply attack fallback)
          (fun entry => ¬ForwardFresh initial entry.2.2.1.state.1) +
        eventProb (coupledCoordinateWorlds initial terminal supply attack fallback)
          (fun entry => entry.2.2.2.state.2 = true) := eventProb_or_le _ _ _
    _ ≤ ((2 * (q * blockLimit) * (q * blockLimit + 1) : Nat) : ℝ≥0∞) *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        ((q * Fintype.card Label : Nat) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
      add_le_add (coupled_forward_failure_bound bound initial terminal supply nodup fallback)
        (coupled_online_guess_bound initial terminal supply bound.queries fallback)
    _ = _ := by rw [Nat.cast_add, add_mul]

/-- In the concrete common probability space, a never-hit ideal execution has
stable literal parents. The fixed coordinate function's injectivity and IV
avoidance are explicit conditions, not assumptions about all sampled functions. -/
theorem coupled_literal_stable (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result) (fallback : Digest)
    (entry : (Label → Digest) ×
      (({message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest) ×
      (Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label) ×
       Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label × Bool))))
    (support : entry ∈ (coupledCoordinateWorlds initial terminal supply attack fallback).support)
    (injective : Function.Injective entry.1) (avoid : ∀ label, entry.1 label ≠ initial)
    (noHit : entry.2.2.2.state.2 = false) :
    ∀ edge ∈ entry.2.2.2.state.1.1.graph, ∀ literal, edge.1.1 = .inl literal →
      latentParent initial entry.2.2.2.state.1.1 literal = .inl literal := by
  unfold coupledCoordinateWorlds at support
  rw [PMF.mem_support_bind_iff] at support
  obtain ⟨coordinates, _, support⟩ := support
  rw [PMF.mem_support_bind_iff] at support
  obtain ⟨hashes, _, support⟩ := support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨pair, reachable, rfl⟩ := support
  let hashOracle := RandomOracle.eager (RandomOracle.extendFinite
    (coordinateHashDomain initial terminal supply attack) fallback hashes)
  have marginal := (Program.coupledRun_marginals
    (coordinateRealWorld initial terminal (RandomOracle.eager coordinates) hashOracle)
    (Program.monitorOracle (latentGuessHit coordinates)
      (latentCoordinateWorld initial terminal (RandomOracle.eager coordinates) hashOracle))
    attack ([], ((supply, false), ([], []))) ((LatentState.empty supply, ([], [])), false)).2
  have supported : pair.2 ∈ (attack.run (Program.monitorOracle (latentGuessHit coordinates)
      (latentCoordinateWorld initial terminal (RandomOracle.eager coordinates) hashOracle))
      ((LatentState.empty supply, ([], [])), false)).support := by
    rw [← marginal, PMF.mem_support_map_iff]
    exact ⟨pair, reachable, rfl⟩
  exact latent_monitored_run_literal_stable initial terminal supply coordinates injective avoid hashOracle
    attack pair.2 supported noHit

/-- The retained coordinate function has its original finite uniform marginal,
even though both adaptive experiments inspect some of its coordinates. -/
theorem coupled_coordinates_marginal (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result) (fallback : Digest) :
    (coupledCoordinateWorlds initial terminal supply attack fallback).map Prod.fst = uniform (Label → Digest) := by
  have const {A B : Type} (law : PMF A) (value : B) : law.map (fun _ => value) = PMF.pure value := by
    change law.map (Function.const A value) = _
    exact PMF.map_const _ _
  unfold coupledCoordinateWorlds
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  simp_rw [const, PMF.bind_const]
  exact PMF.bind_pure _

/-- Global coordinate collisions and a coordinate equal to the IV have their
finite-function birthday bound in this same concrete probability space. -/
theorem coupled_coordinates_bad_bound (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result) (fallback : Digest) :
    eventProb (coupledCoordinateWorlds initial terminal supply attack fallback)
      (fun entry => ¬(Function.Injective entry.1 ∧ ∀ label, entry.1 label ≠ initial)) ≤
      ((Fintype.card Label * (Fintype.card Label + 1) : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have same := congrArg (fun law => eventProb law
      (fun function => ¬(Function.Injective function ∧ ∀ label, function label ≠ initial)))
    (coupled_coordinates_marginal initial terminal supply attack fallback)
  simp only [eventProb_map] at same
  rw [same]
  exact RandomOracle.uniform_function_bad_bound initial

/-- Three specified failure events have an explicit common-law bound.
The missing paired-state preservation theorem must still show that excluding
these failures forces transcript agreement; no such implication is assumed. -/
theorem coupled_coordinate_or_forward_or_guess_bound {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) (supply : List Label) (nodup : supply.Nodup) (fallback : Digest) :
    eventProb (coupledCoordinateWorlds initial terminal supply attack fallback)
      (fun entry => ¬(Function.Injective entry.1 ∧ ∀ label, entry.1 label ≠ initial) ∨
        ¬ForwardFresh initial entry.2.2.1.state.1 ∨ entry.2.2.2.state.2 = true) ≤
      ((Fintype.card Label * (Fintype.card Label + 1) +
        (2 * (q * blockLimit) * (q * blockLimit + 1) + q * Fintype.card Label) : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ eventProb (coupledCoordinateWorlds initial terminal supply attack fallback)
          (fun entry => ¬(Function.Injective entry.1 ∧ ∀ label, entry.1 label ≠ initial)) +
        eventProb (coupledCoordinateWorlds initial terminal supply attack fallback)
          (fun entry => ¬ForwardFresh initial entry.2.2.1.state.1 ∨ entry.2.2.2.state.2 = true) := eventProb_or_le _ _ _
    _ ≤ ((Fintype.card Label * (Fintype.card Label + 1) : Nat) : ℝ≥0∞) *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        ((2 * (q * blockLimit) * (q * blockLimit + 1) + q * Fintype.card Label : Nat) : ℝ≥0∞) *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
      add_le_add (coupled_coordinates_bad_bound initial terminal supply attack fallback)
        (coupled_forward_or_guess_bound bound initial terminal supply nodup fallback)
    _ = _ := by simp only [Nat.cast_add, add_mul]

/-- The existing real instrumentation and its hidden-terminal invariant apply
inside this concrete joint experiment whenever the outer histories still agree.
The monitor is erased only for support transport; its historical flag remains
in the joint law used by the already proved failure-probability bounds. -/
theorem coupled_public_witness (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result) (fallback : Digest)
    (entry : (Label → Digest) ×
      (({message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest) ×
      (Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label) ×
       Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label × Bool))))
    (support : entry ∈ (coupledCoordinateWorlds initial terminal supply attack fallback).support)
    (traces : entry.2.2.1.trace = entry.2.2.2.trace) :
    ∃ tracked : Outcome (WorldInput Payload Digest) Digest Result (TrackedRealState Payload Digest),
      tracked ∈ (attack.run (trackedRealWorld initial terminal) TrackedRealState.empty).support ∧
      Program.mapState TrackedRealState.full tracked = Program.mapState Prod.fst entry.2.2.1 ∧
      tracked.state.exposed = entry.2.2.2.state.1.1.exposed ∧
      PublicConsistent tracked.state ∧ HiddenTerminalsComplete initial terminal tracked.state := by
  unfold coupledCoordinateWorlds at support
  rw [PMF.mem_support_bind_iff] at support
  obtain ⟨coordinates, _, support⟩ := support
  rw [PMF.mem_support_bind_iff] at support
  obtain ⟨hashes, _, support⟩ := support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨pair, reachable, rfl⟩ := support
  let hashOracle := RandomOracle.eager (RandomOracle.extendFinite
    (coordinateHashDomain initial terminal supply attack) fallback hashes)
  have marginals := Program.coupledRun_marginals
    (coordinateRealWorld initial terminal (RandomOracle.eager coordinates) hashOracle)
    (Program.monitorOracle (latentGuessHit coordinates)
      (latentCoordinateWorld initial terminal (RandomOracle.eager coordinates) hashOracle))
    attack ([], ((supply, false), ([], []))) ((LatentState.empty supply, ([], [])), false)
  have realSupport : pair.1 ∈ (attack.run
      (coordinateRealWorld initial terminal (RandomOracle.eager coordinates) hashOracle)
      ([], ((supply, false), ([], [])))).support := by
    rw [← marginals.1, PMF.mem_support_map_iff]
    exact ⟨pair, reachable, rfl⟩
  have monitoredSupport : pair.2 ∈ (attack.run
      (Program.monitorOracle (latentGuessHit coordinates)
        (latentCoordinateWorld initial terminal (RandomOracle.eager coordinates) hashOracle))
      ((LatentState.empty supply, ([], [])), false)).support := by
    rw [← marginals.2, PMF.mem_support_map_iff]
    exact ⟨pair, reachable, rfl⟩
  have idealSupport : Program.mapState Prod.fst pair.2 ∈ (attack.run
      (latentCoordinateWorld initial terminal (RandomOracle.eager coordinates) hashOracle)
      (LatentState.empty supply, ([], []))).support := by
    rw [← Program.monitor_run_erase (latentGuessHit coordinates)
      (latentCoordinateWorld initial terminal (RandomOracle.eager coordinates) hashOracle)
      attack (LatentState.empty supply, ([], [])) false, PMF.mem_support_map_iff]
    exact ⟨pair.2, monitoredSupport, rfl⟩
  exact coordinate_equal_history_witness initial terminal (RandomOracle.eager coordinates)
    (RandomOracle.eager coordinates) hashOracle hashOracle ((supply, false), ([], [])) supply [] []
    attack pair.1 (Program.mapState Prod.fst pair.2) realSupport idealSupport traces

/-- The real world's own private hash cache covers every completed terminal
chain in the concrete joint law outside real graph failure. This conclusion
needs neither equal outer traces nor any assumption about the ideal cache. -/
theorem coupled_real_terminal (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result) (fallback : Digest)
    (entry : (Label → Digest) ×
      (({message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest) ×
      (Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label) ×
       Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label × Bool))))
    (support : entry ∈ (coupledCoordinateWorlds initial terminal supply attack fallback).support)
    (good : ForwardFresh initial entry.2.2.1.state.1) :
    TerminalConsistent initial terminal entry.2.2.1.state.1 entry.2.2.1.state.2.2.1 := by
  exact coordinate_real_terminal_from_empty initial terminal (RandomOracle.eager entry.1)
    (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback entry.2.1)
    attack ((supply, false), ([], [])) entry.2.2.1
    (coupled_coordinate_support initial terminal supply attack fallback entry support).1 good.data

/-- The actual real private hash cache agrees with the shared finite hash
function throughout the joint execution. Its queried keys need not coincide
with those of the ideal world's cache. -/
theorem coupled_real_hash_values (initial : Digest) (terminal : Payload) (supply : List Label)
    (attack : Program (WorldInput Payload Digest) Digest Result) (fallback : Digest)
    (entry : (Label → Digest) ×
      (({message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest) ×
      (Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label) ×
       Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label × Bool))))
    (support : entry ∈ (coupledCoordinateWorlds initial terminal supply attack fallback).support) :
    RandomOracle.TableValues
      (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback entry.2.1)
      entry.2.2.1.state.2.2.1 := by
  exact coordinate_real_run_hash_values initial terminal (RandomOracle.eager entry.1)
    (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback entry.2.1)
    attack ([], ((supply, false), ([], []))) (by intro item member; cases member) entry.2.2.1
    (coupled_coordinate_support initial terminal supply attack fallback entry support).1

/-- In the actual joint law, every unconsumed real label is absent from its
coordinate cache and every allocated cache value agrees with the sampled
coordinate function. This needs no response or transcript equality. -/
theorem coupled_real_allocation_invariants (initial : Digest) (terminal : Payload) (supply : List Label)
    (nodup : supply.Nodup) (attack : Program (WorldInput Payload Digest) Digest Result) (fallback : Digest)
    (entry : (Label → Digest) ×
      (({message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest) ×
      (Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label) ×
       Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label × Bool))))
    (support : entry ∈ (coupledCoordinateWorlds initial terminal supply attack fallback).support) :
    RealCoordinateValid entry.2.2.1.state.2 ∧ RandomOracle.TableValues entry.1 entry.2.2.1.state.2.2.2 := by
  exact coordinate_real_allocation_from_empty initial terminal entry.1
    (RandomOracle.eager (RandomOracle.extendFinite
      (coordinateHashDomain initial terminal supply attack) fallback entry.2.1))
    attack supply nodup false [] [] entry.2.2.1
    (coupled_coordinate_support initial terminal supply attack fallback entry support).1

/-- All ideal-side structural conditions and fixed-hash agreement hold in the
actual joint experiment under explicit capacity. No collision exclusion or
transcript equality is needed; the historical monitor remains in the joint law. -/
theorem coupled_ideal_structural {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) (supply : List Label) (nodup : supply.Nodup)
    (available : q * blockLimit ≤ supply.length) (fallback : Digest)
    (entry : (Label → Digest) ×
      (({message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest) ×
      (Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label) ×
       Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label × Bool))))
    (support : entry ∈ (coupledCoordinateWorlds initial terminal supply attack fallback).support) :
    LatentCoherent entry.2.2.2.state.1 ∧
      RandomOracle.TableValues entry.1 entry.2.2.2.state.1.1.revealed ∧
      entry.2.2.2.state.1.1.AllocationValid ∧ entry.2.2.2.state.1.1.ChildrenUnique ∧
      entry.2.2.2.state.1.1.overflow = false ∧
      supply.length ≤ entry.2.2.2.state.1.1.supply.length + q * blockLimit ∧
      RandomOracle.TableValues
        (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback entry.2.1)
        entry.2.2.2.state.1.2.1 := by
  let hashFunction := RandomOracle.extendFinite
    (coordinateHashDomain initial terminal supply attack) fallback entry.2.1
  have monitored := (coupled_coordinate_support initial terminal supply attack fallback entry support).2
  have idealSupport : Program.mapState Prod.fst entry.2.2.2 ∈ (attack.run
      (latentCoordinateWorld initial terminal (RandomOracle.eager entry.1) (RandomOracle.eager hashFunction))
      (LatentState.empty supply, ([], []))).support := by
    rw [← Program.monitor_run_erase (latentGuessHit entry.1)
      (latentCoordinateWorld initial terminal (RandomOracle.eager entry.1) (RandomOracle.eager hashFunction))
      attack (LatentState.empty supply, ([], [])) false, PMF.mem_support_map_iff]
    exact ⟨entry.2.2.2, monitored, rfl⟩
  have structural := latent_coordinate_structural_from_empty bound initial terminal entry.1
    (RandomOracle.eager hashFunction) supply nodup available (Program.mapState Prod.fst entry.2.2.2) idealSupport
  have values := latent_coordinate_run_hash_values initial terminal (RandomOracle.eager entry.1)
    hashFunction attack (LatentState.empty supply, ([], [])) (by intro item member; cases member)
    (Program.mapState Prod.fst entry.2.2.2) idealSupport
  exact ⟨structural.1, structural.2.1, structural.2.2.1, structural.2.2.2.1,
    structural.2.2.2.2.1, structural.2.2.2.2.2, values⟩

end Foundation.Hash
