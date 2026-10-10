import Foundation.Constructions.Hash.LatentStructure

/-! The complete paired-state induction invariant for actual coordinate worlds.
It bundles previously proved structural conditions, the private-cache facts and
a genuine real proof record. Preservation below derives every next-state field;
chronological freshness and the current monitor test remain explicit guards. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
set_option backward.isDefEq.respectTransparency false
variable {Payload Digest Label : Type} [DecidableEq Payload] [DecidableEq Digest]
  [DecidableEq Label] [Fintype Digest] [Nonempty Digest] [Fintype Label]

structure CoordinatePairInvariant (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (hashFunction : List Payload → Digest)
    (tracked : TrackedRealState Payload Digest)
    (source : CoordinateRealState Payload Digest Label) (ideal : LatentWorldState Payload Digest Label) : Prop where
  full : tracked.full = source.1
  publicEq : tracked.exposed = ideal.1.exposed
  publicConsistent : PublicConsistent tracked
  paths : ExposedPaths initial tracked
  hiddenComplete : HiddenTerminalsComplete initial terminal tracked
  notGuessed : tracked.guessed = false
  relation : LatentDataRelation function source.1 ideal.1
  consistent : RandomOracle.TableConsistent source.1
  supply : source.2.1.1 = ideal.1.supply
  realValid : RealCoordinateValid source.2
  realCoordinateValues : RandomOracle.TableValues function source.2.2.2
  covered : TerminalConsistent initial terminal source.1 source.2.2.1
  realHashValues : RandomOracle.TableValues hashFunction source.2.2.1
  coherent : LatentCoherent ideal
  values : RandomOracle.TableValues function ideal.1.revealed
  allocation : ideal.1.AllocationValid
  unique : ideal.1.ChildrenUnique
  separate : ideal.1.LiteralAvoids function
  noOverflow : ideal.1.overflow = false
  idealHashValues : RandomOracle.TableValues hashFunction ideal.2.1

omit [Fintype Digest] [Nonempty Digest] [Fintype Label] in
/-- Every field of the common paired invariant holds at the actual empty
initial states. Distinct supply labels suffice; no collision assumption is
needed until an actual query is compared. -/
theorem coordinate_pair_invariant_empty (initial : Digest) (terminal : Payload)
    (function : Label → Digest) (hashFunction : List Payload → Digest)
    (supply : List Label) (nodup : supply.Nodup) :
    CoordinatePairInvariant initial terminal function hashFunction TrackedRealState.empty
      ([], ((supply, false), ([], []))) (LatentState.empty supply, ([], [])) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, ?_, ?_, rfl,
    ?_, ?_, TerminalConsistent.empty initial terminal [], ?_, latent_empty_coherent supply,
    ?_, latent_empty_allocation supply nodup, ?_, latent_empty_literal_avoids function supply, rfl, ?_⟩
  · intro entry member; cases member
  · intro blocks target chain entry member; cases member
  · intro entry member; cases member
  · refine ⟨?_, ?_, ?_⟩
    · simp [latentDecodedGraph, LatentState.empty]
    · intro entry member; cases member
    · intro edge member; cases member
  · intro entry member; cases member
  · exact ⟨nodup, by intro label member; rfl⟩
  · intro entry member; cases member
  · intro entry member; cases member
  · intro entry member; cases member
  · intro left member; cases member
  · intro entry member; cases member

/-- Under the current no-guess and chronological-freshness guards, one actual
bounded outer query returns equal responses and preserves the entire paired
invariant and capacity for the remaining q calls. No next-state invariant or
response equality is assumed. -/
theorem coordinate_pair_invariant_step {Result : Type} {blockLimit q : Nat}
    {request : WorldInput Payload Digest} {next : Digest → Program (WorldInput Payload Digest) Digest Result}
    (bound : WorldBound blockLimit (.query request next) (q + 1))
    (initial : Digest) (terminal : Payload) (function : Label → Digest)
    (injective : Function.Injective function) (avoid : ∀ label, function label ≠ initial)
    (hashFunction : List Payload → Digest)
    (tracked : TrackedRealState Payload Digest)
    (source : CoordinateRealState Payload Digest Label) (ideal : LatentWorldState Payload Digest Label)
    (invariant : CoordinatePairInvariant initial terminal function hashFunction tracked source ideal)
    (available : (q + 1) * blockLimit ≤ ideal.1.supply.length)
    (beforeGood : ForwardFresh initial source.1)
    (noHit : latentGuessHit function ideal request = false)
    (realAnswer : CoordinateRealState Payload Digest Label × Digest)
    (idealAnswer : LatentWorldState Payload Digest Label × Digest)
    (realSupport : realAnswer ∈ (coordinateRealWorld initial terminal (RandomOracle.eager function)
      (RandomOracle.eager hashFunction) source request).support)
    (idealSupport : idealAnswer ∈ (latentCoordinateWorld initial terminal (RandomOracle.eager function)
      (RandomOracle.eager hashFunction) ideal request).support)
    (afterGood : ForwardFresh initial realAnswer.1.1) :
    realAnswer.2 = idealAnswer.2 ∧
      (∃ nextTracked, CoordinatePairInvariant initial terminal function hashFunction nextTracked realAnswer.1 idealAnswer.1) ∧
      q * blockLimit ≤ idealAnswer.1.1.supply.length := by
  have capacity := latent_coordinate_step_capacity bound initial terminal function (RandomOracle.eager hashFunction)
    ideal invariant.allocation available idealAnswer idealSupport
  have sourceForm : source = (tracked.full,
      ((ideal.1.supply, source.2.1.2), (source.2.2.1, source.2.2.2))) := by
    change (source.1, ((source.2.1.1, source.2.1.2), (source.2.2.1, source.2.2.2))) = _
    rw [← invariant.full, invariant.supply]
  have idealForm : ideal = (ideal.1, (ideal.2.1, ideal.1.revealed)) := by
    change (ideal.1, (ideal.2.1, ideal.2.2)) = _
    rw [invariant.coherent.1]
  have realSupported := realSupport
  rw [sourceForm] at realSupported
  have idealSupported := idealSupport
  rw [idealForm] at idealSupported
  have paired := coordinate_pair_step initial terminal function injective avoid hashFunction tracked ideal.1
    invariant.publicEq invariant.publicConsistent invariant.paths invariant.hiddenComplete
    (by simpa only [invariant.full] using beforeGood)
    (by simpa only [invariant.full] using invariant.relation)
    (by simpa only [invariant.full] using invariant.consistent)
    invariant.allocation invariant.coherent.2 invariant.unique invariant.values invariant.separate invariant.noOverflow
    source.2.2.1 ideal.2.1 source.2.2.2 source.2.1.2
    (by intro label member; apply invariant.realValid.2 label; rwa [invariant.supply])
    (by simpa only [invariant.full] using invariant.covered) invariant.realHashValues invariant.idealHashValues invariant.notGuessed
    request (by rw [← idealForm]; exact noHit)
    (by cases request <;> simpa only [latentRequestCost] using capacity.1)
    realAnswer idealAnswer realSupported idealSupported afterGood
  obtain ⟨trackedAnswer, trackedSupport, trackedSame, publicAfter, consistentPublic, hiddenAfter, notGuessedAfter, pathsAfter⟩ := paired.2.2.2
  have fullAfter : trackedAnswer.1.full = realAnswer.1.1 := congrArg Prod.fst trackedSame
  let realOut : Outcome (WorldInput Payload Digest) Digest Digest (CoordinateRealState Payload Digest Label) :=
    ⟨realAnswer.2, realAnswer.1, [(request, realAnswer.2)]⟩
  have realReachable : realOut ∈ ((Program.query request Program.done).run
      (coordinateRealWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction)) source).support := by
    rw [Program.run, PMF.mem_support_bind_iff]
    refine ⟨realAnswer, realSupport, ?_⟩
    simp [Program.run, realOut]
  let idealOut : Outcome (WorldInput Payload Digest) Digest Digest (LatentWorldState Payload Digest Label) :=
    ⟨idealAnswer.2, idealAnswer.1, [(request, idealAnswer.2)]⟩
  have idealReachable : idealOut ∈ ((Program.query request Program.done).run
      (latentCoordinateWorld initial terminal (RandomOracle.eager function) (RandomOracle.eager hashFunction)) ideal).support := by
    rw [Program.run, PMF.mem_support_bind_iff]
    refine ⟨idealAnswer, idealSupport, ?_⟩
    simp [Program.run, idealOut]
  have realAllocation := coordinate_real_run_allocation_invariants initial terminal function
    (RandomOracle.eager hashFunction) (Program.query request Program.done) source
    ⟨invariant.realValid, invariant.realCoordinateValues⟩ realOut realReachable
  have coveredAfter := coordinate_real_run_terminal initial terminal (RandomOracle.eager function)
    hashFunction (Program.query request Program.done) source realOut realReachable invariant.covered afterGood.data
  have realHashAfter := coordinate_real_run_hash_values initial terminal (RandomOracle.eager function)
    hashFunction (Program.query request Program.done) source invariant.realHashValues realOut realReachable
  have idealStructural := latent_coordinate_run_structural initial terminal function (RandomOracle.eager hashFunction)
    (Program.query request Program.done) ideal
    ⟨invariant.coherent, invariant.values, invariant.allocation, invariant.unique⟩ idealOut idealReachable
  have idealHashAfter := latent_coordinate_step_hash_values initial terminal (RandomOracle.eager function)
    hashFunction ideal invariant.idealHashValues request idealAnswer idealSupport
  have separateAfter := latent_coordinate_step_literal_avoids initial terminal function injective avoid ideal
    invariant.values invariant.separate request
    (by intro input same; rw [same] at noHit; exact latentGuessHit_no_guess function ideal input noHit)
    (RandomOracle.eager function) (RandomOracle.eager hashFunction) idealAnswer idealSupport
  have consistentAfter := trackedReal_step_table_consistent initial terminal tracked
    (by simpa only [invariant.full] using invariant.consistent) request trackedAnswer trackedSupport
  rw [fullAfter] at consistentAfter
  refine ⟨paired.1, ⟨trackedAnswer.1, ?_⟩, capacity.2.1⟩
  exact ⟨fullAfter, publicAfter, consistentPublic, pathsAfter, hiddenAfter, notGuessedAfter,
    paired.2.1, consistentAfter, paired.2.2.1, realAllocation.1, realAllocation.2,
    coveredAfter, realHashAfter, idealStructural.1, idealStructural.2.1,
    idealStructural.2.2.1, idealStructural.2.2.2, separateAfter,
    capacity.2.2.trans invariant.noOverflow, idealHashAfter⟩

end Foundation.Hash
