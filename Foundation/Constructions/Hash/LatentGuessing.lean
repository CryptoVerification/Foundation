import Foundation.Constructions.Hash.LatentIdeal
import Foundation.Crypto.Semantics.Oracle.QueryMonitor

/-! Online hidden-coordinate guessing in the actual symbolic ideal execution.
A query prefix ends immediately before a public query. Finite-coordinate posterior
laws bound that query's guess, and the state-dependent monitor union bound
covers all public queries, including values revealed later in the interaction.
Transfer to the real compression experiment still needs a coupling invariant. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label]
  [Fintype Digest] [Nonempty Digest] [Fintype Label]

/-- Only a public compression request supplies a chaining-value guess.
High-level requests and termination supply no guesses at this boundary. -/
def nextLowGuesses : Option (WorldInput Payload Digest) → List Digest
  | some (.inr input) => [input.1]
  | _ => []

omit [DecidableEq Payload] [DecidableEq Digest] [DecidableEq Label]
  [Fintype Digest] [Nonempty Digest] [Fintype Label] in
theorem nextLowGuesses_length (request : Option (WorldInput Payload Digest)) :
    (nextLowGuesses request).length ≤ 1 := by
  cases request with
  | none => simp [nextLowGuesses]
  | some request => cases request <;> simp [nextLowGuesses]

/-- The test reads the finite eager function only in proof instrumentation.
The attacker and the symbolic controller never receive that function or flag.
The conservative test includes unused supply coordinates as well as reserved
hidden vertices; this only increases the resulting probability bound. -/
noncomputable def latentGuessHit (function : Label → Digest)
    (state : LatentWorldState Payload Digest Label) (request : WorldInput Payload Digest) : Bool :=
  decide (∃ label ∈ unrevealedLabels state.1, function label ∈ nextLowGuesses (some request))

omit [DecidableEq Payload] [Fintype Digest] [Nonempty Digest] in
theorem latent_prefixHit_iff (function : Label → Digest)
    (out : Outcome (WorldInput Payload Digest) Digest (Option (WorldInput Payload Digest))
      (LatentWorldState Payload Digest Label)) :
    Program.prefixHit (latentGuessHit function) out ↔
      ∃ label ∈ unrevealedLabels out.state.1, function label ∈ nextLowGuesses out.result := by
  cases result : out.result with
  | none => simp [Program.prefixHit, result, nextLowGuesses]
  | some request => simp [Program.prefixHit, result, latentGuessHit]

/-- Each actual query prefix has the same finite-coordinate bound, even though
its request and controller state depend on all earlier public responses. -/
theorem latent_prefix_guess_bound {Result : Type} (initial : Digest) (terminal : Payload)
    (supply : List Label) (attack : Program (WorldInput Payload Digest) Digest Result) (k : Nat)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    eventProb ((uniform (Label → Digest)).bind (fun function =>
      ((Program.queryPrefix k attack).run
        (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle)
        (LatentState.empty supply, ([], []))).map (fun out => (function, out))))
      (fun pair => Program.prefixHit (latentGuessHit pair.1) pair.2) ≤
      (Fintype.card Label : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  let stopped := Program.queryPrefix k attack
  have bound := latent_unrevealed_guess_bound initial terminal supply stopped hashOracle
    (fun out => nextLowGuesses out.result.2) 1 (fun out _ => nextLowGuesses_length out.result.2)
  have same :
      (uniform (Label → Digest)).bind (fun function =>
        (stopped.run (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle)
          (LatentState.empty supply, ([], []))).map (fun out => ((out.state.1, out.result), function))) =
      (uniform (Label → Digest)).bind (fun function =>
        ((latentCompiled initial terminal (LatentState.empty supply) stopped).run
          (RandomOracle.withContext (simulatorBackend hashOracle) (RandomOracle.eager function)) ([], [])).map
          (fun out => (out.result, function))) := by
    congr 1
    funext function
    have h := congrArg (PMF.map (fun pair => (pair.2, function)))
      (latent_compiled_coordinates initial terminal stopped (LatentState.empty supply) ([], [])
        (RandomOracle.eager function) hashOracle)
    simpa only [PMF.map_comp, Program.resultState, Function.comp_def] using h.symm
  have projectedBound : eventProb ((uniform (Label → Digest)).bind (fun function =>
      (stopped.run (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle)
        (LatentState.empty supply, ([], []))).map (fun out => ((out.state.1, out.result), function))))
      (fun pair => ∃ label ∈ unrevealedLabels pair.1.1, pair.2 label ∈ nextLowGuesses pair.1.2) ≤
      (Fintype.card Label : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
    rw [same]
    simpa only [Nat.mul_one, eventProb_bind_eq, eventProb_map] using bound
  have eventSame : eventProb ((uniform (Label → Digest)).bind (fun function =>
      (stopped.run (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle)
        (LatentState.empty supply, ([], []))).map (fun out => (function, out))))
      (fun pair => Program.prefixHit (latentGuessHit pair.1) pair.2) =
      eventProb ((uniform (Label → Digest)).bind (fun function =>
        (stopped.run (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle)
          (LatentState.empty supply, ([], []))).map (fun out => ((out.state.1, out.result), function))))
        (fun pair => ∃ label ∈ unrevealedLabels pair.1.1, pair.2 label ∈ nextLowGuesses pair.1.2) := by
    rw [eventProb_bind_eq, eventProb_bind_eq]
    apply tsum_congr
    intro function
    congr 1
    rw [eventProb_map, eventProb_map]
    congr 1
    funext out
    exact propext (latent_prefixHit_iff function out)
  exact eventSame.le.trans projectedBound

/-- Online bound: any of q adaptive public queries guesses an unrevealed
finite coordinate with probability at most q*N/|Digest|. Later publication of
the guessed coordinate does not remove the earlier hit from this event. -/
theorem latent_first_guess_bound {Result : Type} (initial : Digest) (terminal : Payload)
    (supply : List Label) {attack : Program (WorldInput Payload Digest) Digest Result} {q : Nat}
    (bound : attack.BoundedQueries q)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    eventProb ((uniform (Label → Digest)).bind (fun function =>
      Program.firstHit (latentGuessHit function)
        (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle)
        (LatentState.empty supply, ([], [])) attack)) (· = true) ≤
      ((q * Fintype.card Label : Nat) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have h := Program.firstHit_mixed_bound (uniform (Label → Digest))
    (fun function => latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle) latentGuessHit
    bound (LatentState.empty supply, ([], []))
    ((Fintype.card Label : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹)
    (fun k _ => latent_prefix_guess_bound initial terminal supply attack k hashOracle)
  simpa only [Nat.cast_mul, mul_assoc] using h

/-- The same online bound holds for a flag on the full, unstopped interaction.
The flag is private to the monitor, and its erasure preserves the entire game. -/
theorem latent_online_guess_bound {Result : Type} (initial : Digest) (terminal : Payload)
    (supply : List Label) {attack : Program (WorldInput Payload Digest) Digest Result} {q : Nat}
    (bound : attack.BoundedQueries q)
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest) := RandomOracle.oracle) :
    eventProb ((uniform (Label → Digest)).bind (fun function =>
      (attack.run (Program.monitorOracle (latentGuessHit function)
        (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle))
        ((LatentState.empty supply, ([], [])), false)).map (fun out => out.state.2))) (· = true) ≤
      ((q * Fintype.card Label : Nat) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have law : (uniform (Label → Digest)).bind (fun function =>
      (attack.run (Program.monitorOracle (latentGuessHit function)
        (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle))
        ((LatentState.empty supply, ([], [])), false)).map (fun out => out.state.2)) =
      (uniform (Label → Digest)).bind (fun function =>
        Program.firstHit (latentGuessHit function)
          (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle)
          (LatentState.empty supply, ([], [])) attack) := by
    congr 1
    funext function
    exact (Program.monitor_firstHit (latentGuessHit function)
      (latentCoordinateWorld initial terminal (RandomOracle.eager function) hashOracle) attack
      (LatentState.empty supply, ([], [])) false).trans (by
        change PMF.map id _ = _
        exact PMF.map_id _)
  rw [law]
  exact latent_first_guess_bound initial terminal supply bound hashOracle

/-- Integrating the finite eager function recovers the symbolic lazy experiment
with its joint final controller state, backend state and attacker result. -/
theorem latent_eager_run {Result : Type} (initial : Digest) (terminal : Payload)
    (supply : List Label) (attack : Program (WorldInput Payload Digest) Digest Result) :
    (uniform (Label → Digest)).bind (fun function =>
      (attack.run (latentCoordinateWorld initial terminal (RandomOracle.eager function))
        (LatentState.empty supply, ([], []))).map Program.resultState) =
      (attack.run (latentWorld initial terminal) (LatentState.empty supply, ([], []))).map Program.resultState := by
  let compiled := latentCompiled initial terminal (LatentState.empty supply) attack
  have mixed := congrArg (PMF.map (fun out => (out.state, out.result)))
    (RandomOracle.eager_lazy_context (simulatorBackend RandomOracle.oracle) compiled [] [])
  simp only [PMF.map_bind] at mixed
  have lowered (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest)) :
      (compiled.run (RandomOracle.withContext (simulatorBackend RandomOracle.oracle) coordinates) ([], [])).map
        (fun out => (out.state, out.result)) =
      (attack.run (latentCoordinateWorld initial terminal coordinates)
        (LatentState.empty supply, ([], []))).map
        (fun out => (out.state.2, (out.state.1, out.result))) :=
    latent_compiled_coordinates initial terminal attack (LatentState.empty supply) ([], []) coordinates
  simp_rw [lowered] at mixed
  have unpacked := congrArg (PMF.map (fun pair => ((pair.2.1, pair.1), pair.2.2))) mixed
  unfold Program.resultState
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def,
    latent_coordinate_lazy, Prod.mk.eta] using unpacked

/-- The online-guess experiment's eager backend has the same attacker-result
law as the original fixed candidate. This equality does not give the candidate
access to its proof instrumentation or to the hidden finite function. -/
theorem latent_eager_candidate_result {Result : Type} (initial : Digest) (terminal : Payload)
    (supply : List Label) (attack : Program (WorldInput Payload Digest) Digest Result) :
    (uniform (Label → Digest)).bind (fun function =>
      (attack.run (latentCoordinateWorld initial terminal (RandomOracle.eager function))
        (LatentState.empty supply, ([], []))).map Outcome.result) =
      (attack.run ((candidate initial terminal).world RandomOracle.oracle) ([], [])).map Outcome.result := by
  have eager := congrArg (PMF.map Prod.snd) (latent_eager_run initial terminal supply attack)
  have candidate := congrArg (PMF.map Outcome.result) (latent_candidate_run initial terminal supply attack)
  simp only [PMF.map_bind, PMF.map_comp, Program.resultState, Function.comp_def] at eager
  simp only [PMF.map_comp, Program.mapState, Function.comp_def] at candidate
  exact eager.trans candidate

/-- Even the complete flagged experiment has exactly the fixed candidate's
attacker-result distribution after forgetting proof instrumentation. -/
theorem latent_monitored_candidate_result {Result : Type} (initial : Digest) (terminal : Payload)
    (supply : List Label) (attack : Program (WorldInput Payload Digest) Digest Result) :
    (uniform (Label → Digest)).bind (fun function =>
      (attack.run (Program.monitorOracle (latentGuessHit function)
        (latentCoordinateWorld initial terminal (RandomOracle.eager function)))
        ((LatentState.empty supply, ([], [])), false)).map Outcome.result) =
      (attack.run ((candidate initial terminal).world RandomOracle.oracle) ([], [])).map Outcome.result := by
  have erased : (uniform (Label → Digest)).bind (fun function =>
      (attack.run (Program.monitorOracle (latentGuessHit function)
        (latentCoordinateWorld initial terminal (RandomOracle.eager function)))
        ((LatentState.empty supply, ([], [])), false)).map Outcome.result) =
      (uniform (Label → Digest)).bind (fun function =>
        (attack.run (latentCoordinateWorld initial terminal (RandomOracle.eager function))
          (LatentState.empty supply, ([], []))).map Outcome.result) := by
    congr 1
    funext function
    have h := congrArg (PMF.map Outcome.result) (Program.monitor_run_erase (latentGuessHit function)
      (latentCoordinateWorld initial terminal (RandomOracle.eager function)) attack
      (LatentState.empty supply, ([], [])) false)
    simpa only [PMF.map_comp, Program.mapState, Function.comp_def] using h
  exact erased.trans (latent_eager_candidate_result initial terminal supply attack)

end Foundation.Hash
