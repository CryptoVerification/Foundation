import Foundation.Constructions.Hash.CoordinateInvariant
import Foundation.Crypto.Semantics.Oracle.CoupledRun
import Foundation.Crypto.Semantics.Oracle.QueryMonitor

/-! Whole adaptive agreement of the actual coordinate worlds outside the
chronological-freshness and monitored-guess failures. The final good conditions
are transported backwards along genuine supported executions, rather than
assuming good states separately at every query. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false
variable {Payload Digest Label Result : Type} [DecidableEq Payload] [DecidableEq Digest]
  [DecidableEq Label] [Fintype Digest] [Nonempty Digest]

omit [DecidableEq Label] in
/-- The actual full compression table only grows; private backend caches are
retained in the source execution and need no equality with ideal caches. -/
theorem coordinate_real_step_extends (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (state : CoordinateRealState Payload Digest Label) (request : WorldInput Payload Digest)
    (answer : CoordinateRealState Payload Digest Label × Digest)
    (support : answer ∈ (coordinateRealWorld initial terminal coordinates hashOracle state request).support) :
    ∃ later : CompressionTable Payload Digest, answer.1.1 = later ++ state.1 := by
  have realSupport := coordinate_real_step_support initial terminal coordinates state request answer support
  cases request with
  | inl message =>
      rw [realWorld, PMF.mem_support_map_iff] at realSupport
      obtain ⟨out, reachable, same⟩ := realSupport
      obtain ⟨later, extended⟩ := RandomOracle.run_table_extends
        (prefixFreeMD initial terminal message) state.1 out reachable
      exact ⟨later, (congrArg Prod.fst same).symm.trans extended⟩
  | inr input => exact RandomOracle.step_table_extends state.1 input _ realSupport

omit [DecidableEq Label] in
/-- Table extension persists through the entire adaptive execution. -/
theorem coordinate_real_run_extends (initial : Digest) (terminal : Payload)
    (coordinates : Oracle Label Digest (RandomOracle.Table Label Digest))
    (hashOracle : Oracle (List Payload) Digest (RandomOracle.Table (List Payload) Digest))
    (attack : Program (WorldInput Payload Digest) Digest Result)
    (state : CoordinateRealState Payload Digest Label)
    (out : Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label))
    (support : out ∈ (attack.run (coordinateRealWorld initial terminal coordinates hashOracle) state).support) :
    ∃ later : CompressionTable Payload Digest, out.state.1 = later ++ state.1 := by
  apply Program.run_preserves _ (fun current => ∃ later, current.1 = later ++ state.1)
    _ attack state ⟨[], rfl⟩ out support
  intro current extended request answer reachable
  obtain ⟨before, beforeEq⟩ := extended
  obtain ⟨later, laterEq⟩ := coordinate_real_step_extends initial terminal coordinates hashOracle
    current request answer reachable
  exact ⟨later ++ before, by rw [laterEq, beforeEq, List.append_assoc]⟩

variable [Fintype Label]

private theorem coordinate_coupled_query_agreement {blockLimit q : Nat}
    {request : WorldInput Payload Digest} {next : Digest → Program (WorldInput Payload Digest) Digest Result}
    (bound : WorldBound blockLimit (.query request next) (q + 1))
    (initial : Digest) (terminal : Payload) (function : Label → Digest)
    (injective : Function.Injective function) (avoid : ∀ label, function label ≠ initial)
    (hashFunction : List Payload → Digest)
    (ih : ∀ response tracked source ideal marked pair,
      CoordinatePairInvariant initial terminal function hashFunction tracked source ideal →
      q * blockLimit ≤ ideal.1.supply.length →
      pair ∈ (Program.coupledRun
        (coordinateRealWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction))
        (Program.monitorOracle (latentGuessHit function)
          (latentCoordinateWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction)))
        source (ideal, marked) (next response)).support →
      ForwardFresh initial pair.1.state.1 → pair.2.state.2 = false → pair.1.trace = pair.2.trace)
    (tracked : TrackedRealState Payload Digest)
    (source : CoordinateRealState Payload Digest Label) (ideal : LatentWorldState Payload Digest Label)
    (marked : Bool)
    (pair : Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label) ×
      Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label × Bool))
    (invariant : CoordinatePairInvariant initial terminal function hashFunction tracked source ideal)
    (available : (q + 1) * blockLimit ≤ ideal.1.supply.length)
    (support : pair ∈ (Program.coupledRun
      (coordinateRealWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction))
      (Program.monitorOracle (latentGuessHit function)
        (latentCoordinateWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction)))
      source (ideal, marked) (.query request next)).support)
    (good : ForwardFresh initial pair.1.state.1) (unmarked : pair.2.state.2 = false) :
    pair.1.trace = pair.2.trace := by
  rw [Program.coupledRun, PMF.mem_support_bind_iff] at support
  obtain ⟨realAnswer, realSupport, support⟩ := support
  rw [PMF.mem_support_bind_iff] at support
  obtain ⟨monitoredAnswer, monitoredSupport, support⟩ := support
  rw [Program.monitorOracle, PMF.mem_support_map_iff] at monitoredSupport
  obtain ⟨idealAnswer, idealSupport, rfl⟩ := monitoredSupport
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨tail, tailSupport, rfl⟩ := support
  have marginals :
      (if realAnswer.2 = idealAnswer.2 then
        Program.coupledRun
          (coordinateRealWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction))
          (Program.monitorOracle (latentGuessHit function)
            (latentCoordinateWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction)))
          realAnswer.1 (idealAnswer.1, marked || latentGuessHit function ideal request) (next realAnswer.2)
      else Program.independentRuns
        ((next realAnswer.2).run (coordinateRealWorld initial terminal (RandomOracle.eager function)
          (RandomOracle.eager hashFunction)) realAnswer.1)
        ((next idealAnswer.2).run (Program.monitorOracle (latentGuessHit function)
          (latentCoordinateWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction)))
          (idealAnswer.1, marked || latentGuessHit function ideal request))).map Prod.fst =
        (next realAnswer.2).run (coordinateRealWorld initial terminal (RandomOracle.eager function)
          (RandomOracle.eager hashFunction)) realAnswer.1 ∧
      (if realAnswer.2 = idealAnswer.2 then
        Program.coupledRun
          (coordinateRealWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction))
          (Program.monitorOracle (latentGuessHit function)
            (latentCoordinateWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction)))
          realAnswer.1 (idealAnswer.1, marked || latentGuessHit function ideal request) (next realAnswer.2)
      else Program.independentRuns
        ((next realAnswer.2).run (coordinateRealWorld initial terminal (RandomOracle.eager function)
          (RandomOracle.eager hashFunction)) realAnswer.1)
        ((next idealAnswer.2).run (Program.monitorOracle (latentGuessHit function)
          (latentCoordinateWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction)))
          (idealAnswer.1, marked || latentGuessHit function ideal request))).map Prod.snd =
        (next idealAnswer.2).run (Program.monitorOracle (latentGuessHit function)
          (latentCoordinateWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction)))
          (idealAnswer.1, marked || latentGuessHit function ideal request) := by
    by_cases same : realAnswer.2 = idealAnswer.2
    · simp only [if_pos same]
      have h := Program.coupledRun_marginals
        (coordinateRealWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction))
        (Program.monitorOracle (latentGuessHit function)
          (latentCoordinateWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction)))
        (next realAnswer.2) realAnswer.1 (idealAnswer.1, marked || latentGuessHit function ideal request)
      exact ⟨h.1, h.2.trans (by rw [same])⟩
    · simp [same]
  have leftSupport : tail.1 ∈ ((next realAnswer.2).run
      (coordinateRealWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction)) realAnswer.1).support := by
    rw [← marginals.1, PMF.mem_support_map_iff]
    exact ⟨tail, tailSupport, rfl⟩
  have rightSupport : tail.2 ∈ ((next idealAnswer.2).run
      (Program.monitorOracle (latentGuessHit function)
        (latentCoordinateWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction)))
      (idealAnswer.1, marked || latentGuessHit function ideal request)).support := by
    rw [← marginals.2, PMF.mem_support_map_iff]
    exact ⟨tail, tailSupport, rfl⟩
  obtain ⟨later, laterEq⟩ := coordinate_real_run_extends initial terminal (RandomOracle.eager function)
    (RandomOracle.eager hashFunction) (next realAnswer.2) realAnswer.1 tail.1 leftSupport
  have afterGood : ForwardFresh initial realAnswer.1.1 := by
    apply RandomOracle.Avoided.append_tail later realAnswer.1.1
    rwa [← laterEq]
  obtain ⟨added, addedEq⟩ := coordinate_real_step_extends initial terminal (RandomOracle.eager function)
    (RandomOracle.eager hashFunction) source request realAnswer realSupport
  have beforeGood : ForwardFresh initial source.1 := by
    apply RandomOracle.Avoided.append_tail added source.1
    rwa [← addedEq]
  have noHit := (Bool.or_eq_false_iff.mp (Program.monitor_run_unmarked (latentGuessHit function)
    (latentCoordinateWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction))
    (next idealAnswer.2) idealAnswer.1 (marked || latentGuessHit function ideal request)
    tail.2 rightSupport unmarked)).2
  obtain ⟨same, ⟨nextTracked, nextInvariant⟩, remaining⟩ := coordinate_pair_invariant_step bound
    initial terminal function injective avoid hashFunction tracked source ideal invariant available beforeGood noHit
    realAnswer idealAnswer realSupport idealSupport afterGood
  rw [if_pos same] at tailSupport
  have traces := ih realAnswer.2 nextTracked realAnswer.1 idealAnswer.1
    (marked || latentGuessHit function ideal request) tail nextInvariant remaining tailSupport good unmarked
  change (request, realAnswer.2) :: tail.1.trace = (request, idealAnswer.2) :: tail.2.trace
  rw [same, traces]

/-- The actual whole coupled execution has equal public traces whenever its
final real table is chronologically fresh and its final ideal monitor is false.
Only the initial capacity is assumed; all later capacities and state conditions
are derived by the paired-step theorem. -/
theorem coordinate_coupled_trace_eq {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) (function : Label → Digest)
    (injective : Function.Injective function) (avoid : ∀ label, function label ≠ initial)
    (hashFunction : List Payload → Digest)
    (tracked : TrackedRealState Payload Digest)
    (source : CoordinateRealState Payload Digest Label) (ideal : LatentWorldState Payload Digest Label)
    (marked : Bool)
    (pair : Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label) ×
      Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label × Bool))
    (invariant : CoordinatePairInvariant initial terminal function hashFunction tracked source ideal)
    (available : q * blockLimit ≤ ideal.1.supply.length)
    (support : pair ∈ (Program.coupledRun
      (coordinateRealWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction))
      (Program.monitorOracle (latentGuessHit function)
        (latentCoordinateWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction)))
      source (ideal, marked) attack).support)
    (good : ForwardFresh initial pair.1.state.1) (unmarked : pair.2.state.2 = false) :
    pair.1.trace = pair.2.trace := by
  induction bound generalizing tracked source ideal marked pair with
  | done result q =>
      rw [Program.coupledRun, PMF.mem_support_pure_iff] at support
      subst pair
      rfl
  | coin next q bounds ih =>
      rw [Program.coupledRun, PMF.mem_support_bind_iff] at support
      obtain ⟨bit, _, reachable⟩ := support
      exact ih bit tracked source ideal marked pair invariant available reachable good unmarked
  | hash message next q length bounds ih =>
      exact coordinate_coupled_query_agreement (.hash message next q length bounds)
        initial terminal function injective avoid hashFunction ih
        tracked source ideal marked pair invariant available support good unmarked
  | compression input next q positive bounds ih =>
      exact coordinate_coupled_query_agreement (.compression input next q positive bounds)
        initial terminal function injective avoid hashFunction ih
        tracked source ideal marked pair invariant available support good unmarked

end Foundation.Hash
