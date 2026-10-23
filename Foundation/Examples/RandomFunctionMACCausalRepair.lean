import Foundation.Examples.CausalCouplingRepair
import Foundation.Examples.RandomFunctionMACRepresentationGame

/-! Timing-of-information repair gap at the actual first MAC query. A private
repair policy may see the caller's coin but must choose before the first tag.
The tag then selects the future cost profile. These are proof repair costs,
not cryptographic success probabilities or machine running times. -/
namespace Foundation.Symmetric.RandomFunctionMACCausalRepair
open Foundation.Probability Foundation.Probability.SelectedCouplingGraph
open CryptoOracle CryptoOracle.RandomOracle
open RandomFunctionMACNativeCaller (firstMessage secondMessage)
open CausalRepair
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

abbrev PrefixOutcome := Outcome (Fin 8) (Fin 256) (Bool × Fin 256) (Table (Fin 8) (Fin 256))

def firstProgram : Program (Fin 8) (Fin 256) (Bool × Fin 256) :=
  .coin fun coin => .query (firstMessage coin) fun tag => .done (coin, tag)

def remaining (pair : Bool × Fin 256) : Program (Fin 8) (Fin 256) Bool :=
  .query (secondMessage pair.2) fun second =>
    .query (firstMessage pair.1) fun repeated => .query 7 fun actual =>
      .done (decide (actual = if pair.1 then repeated else second))

theorem actual_prefix : firstProgram.bind remaining = RandomFunctionMACNativeCaller.target := rfl

def challenge (tag : Fin 256) : Bool := RandomFunctionMACNativeCaller.Backend.tagBits tag 0

theorem challenge_uniform : (uniform (Fin 256)).map challenge = uniform Bool := by
  have coordinate : (uniform (Bits 8)).map (fun bits => bits 0) = uniform Bool := by
    have law := uniform_function_fresh (0 : Fin 8)
      (fun value (_ : Fin 8 → Bool) => PMF.pure value) (by intro _ _; rfl)
    simpa only [PMF.bind_const, PMF.map, Function.comp_def, PMF.bind_pure] using law
  have encoded := congrArg (fun p => p.map (fun bits : Bits 8 => bits 0))
    (uniform_map_equiv RandomFunctionMACNativeCaller.Backend.tagEquiv)
  simp only [PMF.map_comp, Function.comp_def, RandomFunctionMACNativeCaller.Backend.tagEquiv,
    Equiv.coe_fn_mk] at encoded
  exact encoded.trans coordinate

def prefixOutput (coin : Bool) (answer : Table (Fin 8) (Fin 256) × Fin 256) : PrefixOutcome :=
  ⟨(coin, answer.2), answer.1, [(firstMessage coin, answer.2)]⟩

/-- Binding the private policy before the oracle call enforces the information
restriction; the policy cannot take the future response as an argument. -/
noncomputable def beforeFirst (policy : Bool → PMF (Vertex → Bool)) : PMF (PrefixOutcome × (Vertex → Bool)) :=
  sampleBit.bind fun coin => (policy coin).bind fun candidate =>
    (RandomOracle.oracle [] (firstMessage coin)).map fun answer => (prefixOutput coin answer, candidate)

theorem prefix_preserved (policy : Bool → PMF (Vertex → Bool)) :
    (beforeFirst policy).map Prod.fst = firstProgram.run RandomOracle.oracle [] := by
  simp [beforeFirst, firstProgram, Program.run, Function.comp_def,
    PMF.bind_const, PMF.map, prefixOutput]

noncomputable def beforeCost (expensive : Nat) (policy : Bool → PMF (Vertex → Bool)) : PMF Nat :=
  (beforeFirst policy).map fun pair =>
    (Fan.graph 1).cutCost (weights expensive (challenge pair.1.result.2)) pair.2

/-- The real first oracle response, including its adaptive request, supplies
exactly the independent fair profile used by the abstract separation. -/
theorem response_cost_law (expensive : Nat) (coin : Bool) (candidate : Vertex → Bool)
    (valid : candidate (.inr false) ≠ candidate (.inr true)) :
    (RandomOracle.oracle [] (firstMessage coin)).map (fun answer =>
      (Fan.graph 1).cutCost (weights expensive (challenge answer.2)) candidate) = priceLaw expensive := by
  rw [fresh [] (firstMessage coin) rfl, PMF.map_comp]
  simp only [Function.comp_def]
  have law := congrArg (fun p => p.map (fun observed => price expensive observed
    (Bool.xor (candidate (.inr false)) (candidate (.inl 0))))) challenge_uniform
  simp only [PMF.map_comp, Function.comp_def] at law
  simp_rw [cut_price expensive _ candidate valid]
  exact law.trans (fixed_price_law expensive _)

theorem before_cost_law (expensive : Nat) (policy : Bool → PMF (Vertex → Bool))
    (valid : ∀ coin candidate, candidate ∈ (policy coin).support →
      candidate (.inr false) ≠ candidate (.inr true)) :
    beforeCost expensive policy = priceLaw expensive := by
  simp only [beforeCost, beforeFirst, PMF.map_bind, PMF.map_comp, Function.comp_def, prefixOutput]
  calc
    _ = sampleBit.bind (fun _ => priceLaw expensive) := by
      congr 1
      funext coin
      calc
        _ = (policy coin).bind (fun _ => priceLaw expensive) := by
          apply bind_congr_of_support
          intro candidate supported
          exact response_cost_law expensive coin candidate (valid coin candidate supported)
        _ = _ := PMF.bind_const _ _
    _ = _ := PMF.bind_const _ _

noncomputable def afterCost (expensive : Nat) : PMF Nat :=
  (firstProgram.run RandomOracle.oracle []).map fun out =>
    (Fan.graph 1).cutCost (weights expensive (challenge out.result.2)) (cut (!challenge out.result.2))

theorem after_cost_law (expensive : Nat) : afterCost expensive = PMF.pure 1 := by
  unfold afterCost
  simp_rw [after_observation_cost]
  exact PMF.map_const _ _

/-- The same MAC prefix exhibits a separation for EVERY valid randomized
policy committed before the tag, even allowing dependence on the caller coin. -/
theorem timing_gap (expensive : Nat) (different : expensive ≠ 1)
    (policy : Bool → PMF (Vertex → Bool))
    (valid : ∀ coin candidate, candidate ∈ (policy coin).support →
      candidate (.inr false) ≠ candidate (.inr true)) :
    beforeCost expensive policy ≠ afterCost expensive := by
  have impossible := causal_gap expensive different (PMF.pure false)
  rw [independent_price_law, after_price_law] at impossible
  rwa [before_cost_law expensive policy valid, after_cost_law]

abbrev FinalOutcome := Outcome (Fin 8) (Fin 256) Bool (Table (Fin 8) (Fin 256))

noncomputable def continuation (past : PrefixOutcome) : PMF FinalOutcome :=
  ((remaining past.result).run RandomOracle.oracle past.state).map fun last =>
    {last with trace := past.trace ++ last.trace}

/-- Retain the committed cut and first response while continuing the original
remaining three calls. This is one joint through the complete game. -/
noncomputable def fullRun (policy : Bool → PMF (Vertex → Bool)) :
    PMF ((PrefixOutcome × (Vertex → Bool)) × FinalOutcome) :=
  (beforeFirst policy).bind fun pair => (continuation pair.1).map fun out => (pair, out)

theorem full_run_prefix (policy : Bool → PMF (Vertex → Bool)) :
    (fullRun policy).map Prod.fst = beforeFirst policy := by
  simp only [fullRun, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change ((beforeFirst policy).bind fun pair => (continuation pair.1).map (Function.const _ pair)) = _
  simp only [PMF.map_const, PMF.bind_pure]

theorem full_run_game (policy : Bool → PMF (Vertex → Bool)) :
    (fullRun policy).map Prod.snd = RandomFunctionMACNativeCaller.target.run RandomOracle.oracle [] := by
  rw [← actual_prefix, Program.run_bind]
  change (fullRun policy).map Prod.snd = (firstProgram.run RandomOracle.oracle []).bind continuation
  have law := congrArg (fun p => p.bind continuation) (prefix_preserved policy)
  simp only [fullRun, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change ((beforeFirst policy).bind fun pair => (continuation pair.1).map id) = _
  simp only [PMF.map_id]
  simpa only [PMF.bind_map, Function.comp_def] using law

theorem full_run_cost_law (expensive : Nat) (policy : Bool → PMF (Vertex → Bool))
    (valid : ∀ coin candidate, candidate ∈ (policy coin).support →
      candidate (.inr false) ≠ candidate (.inr true)) :
    (fullRun policy).map (fun out =>
      (Fan.graph 1).cutCost (weights expensive (challenge out.1.1.result.2)) out.1.2) = priceLaw expensive := by
  have law := congrArg (fun p => p.map (fun pair : PrefixOutcome × (Vertex → Bool) =>
    (Fan.graph 1).cutCost (weights expensive (challenge pair.1.result.2)) pair.2)) (full_run_prefix policy)
  simp only [PMF.map_comp, Function.comp_def] at law
  exact law.trans (before_cost_law expensive policy valid)

theorem full_run_expensive_probability (expensive : Nat) (different : expensive ≠ 1)
    (policy : Bool → PMF (Vertex → Bool))
    (valid : ∀ coin candidate, candidate ∈ (policy coin).support →
      candidate (.inr false) ≠ candidate (.inr true)) :
    eventProb (fullRun policy) (fun out =>
      (Fan.graph 1).cutCost (weights expensive (challenge out.1.1.result.2)) out.1.2 = expensive) =
        (2 : ℝ≥0∞)⁻¹ := by
  have law := congrArg (fun p => eventProb p (· = expensive))
    (full_run_cost_law expensive policy valid)
  rw [eventProb_map] at law
  have probability := expensive_probability expensive different (PMF.pure false)
  rw [independent_price_law] at probability
  exact law.trans probability

end Foundation.Symmetric.RandomFunctionMACCausalRepair
