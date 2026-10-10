import Foundation.Constructions.Hash.CoupledWorlds
import Foundation.Constructions.Hash.CoordinateAgreement

/-! Quantitative strong indifferentiability in the existing query semantics.
One fixed simulator works for every bounded adaptive two-window distinguisher.
The bounds count oracle calls, not machine transitions or encoded storage. -/
namespace Foundation.Hash

open CryptoOracle Foundation.Probability
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
variable {Payload Digest Label Result : Type} [DecidableEq Payload] [DecidableEq Digest]
  [DecidableEq Label] [Fintype Digest] [Nonempty Digest] [Fintype Label]

/-- In the actual common probability space, excluding the three measured
failure events makes the entire public histories agree. -/
theorem coupled_trace_eq_of_good {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) (supply : List Label) (nodup : supply.Nodup)
    (available : q * blockLimit ≤ supply.length) (fallback : Digest)
    (entry : (Label → Digest) ×
      (({message // message ∈ coordinateHashDomain initial terminal supply attack} → Digest) ×
      (Outcome (WorldInput Payload Digest) Digest Result (CoordinateRealState Payload Digest Label) ×
       Outcome (WorldInput Payload Digest) Digest Result (LatentWorldState Payload Digest Label × Bool))))
    (support : entry ∈ (coupledCoordinateWorlds initial terminal supply attack fallback).support)
    (injective : Function.Injective entry.1) (avoid : ∀ label, entry.1 label ≠ initial)
    (good : ForwardFresh initial entry.2.2.1.state.1) (unmarked : entry.2.2.2.state.2 = false) :
    entry.2.2.1.trace = entry.2.2.2.trace := by
  unfold coupledCoordinateWorlds at support
  rw [PMF.mem_support_bind_iff] at support
  obtain ⟨coordinates, _, support⟩ := support
  rw [PMF.mem_support_bind_iff] at support
  obtain ⟨hashes, _, support⟩ := support
  rw [PMF.mem_support_map_iff] at support
  obtain ⟨pair, reachable, rfl⟩ := support
  exact coordinate_coupled_trace_eq bound initial terminal coordinates injective avoid
    (RandomOracle.extendFinite (coordinateHashDomain initial terminal supply attack) fallback hashes)
    TrackedRealState.empty ([], ((supply, false), ([], []))) ((LatentState.empty supply), ([], []))
    false pair (coordinate_pair_invariant_empty initial terminal _ _ supply nodup)
    available reachable good unmarked

/-- Concrete distinguishing loss, with a proof-only pool of distinct labels.
The private hash window may depend on the distinguisher; the simulator does not.
All events concern the original two public windows, including compression. -/
theorem candidate_gap_bound {blockLimit q : Nat}
    {attack : Program (WorldInput Payload Digest) Digest Result} (bound : WorldBound blockLimit attack q)
    (initial : Digest) (terminal : Payload) (supply : List Label) (nodup : supply.Nodup)
    (available : q * blockLimit ≤ supply.length) (fallback : Digest) (event : Result → Prop) :
    probabilityGap
      (eventProb (attack.run (realWorld initial terminal) []) (fun out => event out.result))
      (eventProb (attack.run ((candidate initial terminal).world RandomOracle.oracle) ([], []))
        (fun out => event out.result)) ≤
      ((Fintype.card Label * (Fintype.card Label + 1) +
        (2 * (q * blockLimit) * (q * blockLimit + 1) + q * Fintype.card Label) : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ eventProb (coupledCoordinateWorlds initial terminal supply attack fallback)
        (fun entry => entry.2.2.1.trace ≠ entry.2.2.2.trace) :=
      coupled_hash_gap_le initial terminal supply nodup attack fallback event
    _ ≤ eventProb (coupledCoordinateWorlds initial terminal supply attack fallback)
        (fun entry => ¬(Function.Injective entry.1 ∧ ∀ label, entry.1 label ≠ initial) ∨
          ¬ForwardFresh initial entry.2.2.1.state.1 ∨ entry.2.2.2.state.2 = true) := by
      apply eventProb_mono_of_support
      intro entry reachable different
      by_contra noFailure
      push Not at noFailure
      have unmarked : entry.2.2.2.state.2 = false := by
        cases flag : entry.2.2.2.state.2 <;> simp_all
      exact different (coupled_trace_eq_of_good bound initial terminal supply nodup available fallback
        entry reachable noFailure.1.1 noFailure.1.2 noFailure.2.1 unmarked)
    _ ≤ _ := coupled_coordinate_or_forward_or_guess_bound bound initial terminal supply nodup fallback

omit [DecidableEq Label] [Fintype Label] in
/-- Prefix-free MD with a terminal marker and a fixed initial value is strongly
query-indifferentiable from a random oracle. The same candidate simulator is
chosen before every adaptive distinguisher; each public compression call makes
at most one internal hash-or-randomness call. The bound includes high-level
hash calls and public compression calls in q, and encoded blocks in blockLimit.
No concrete hash implementation or machine-resource claim follows here. -/
theorem prefixFreeMD_query_indifferentiable (initial : Digest) (terminal : Payload)
    (blockLimit q : Nat) :
    QueryIndifferentiable initial terminal blockLimit q 1
      ((((q * blockLimit) * (q * blockLimit + 1) +
        (2 * (q * blockLimit) * (q * blockLimit + 1) + q * (q * blockLimit)) : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹) := by
  refine ⟨candidate initial terminal, candidate_calls initial terminal, ?_⟩
  intro attack bound
  have gap := candidate_gap_bound bound initial terminal (List.finRange (q * blockLimit))
    (List.nodup_finRange _) (by simp) initial (fun result => result = true)
  simpa only [CryptoOracle.goal, protocol, eventProb_map, Fintype.card_fin, candidate] using gap

end Foundation.Hash
