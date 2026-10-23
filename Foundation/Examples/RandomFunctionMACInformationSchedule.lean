import Foundation.Examples.InformationSchedule
import Foundation.Examples.RandomFunctionMACCausalRepair

/-! The dependency-aware checker at the same actual MAC first-response prefix.
Visibility schedules are proof operations over an already retained response;
they are not new oracle calls or a new native implementation. -/
namespace Foundation.Symmetric.RandomFunctionMACInformationSchedule
open Foundation.Probability Foundation.Probability.SelectedCouplingGraph.CausalRepair
open CryptoOracle CryptoOracle.RandomOracle
open CryptoOracle.InformationSchedule
open RandomFunctionMACCausalRepair
set_option backward.isDefEq.respectTransparency false

abbrev InformationState := InformationSchedule.State Bool Bool Bool

theorem first_profile_law :
    (firstProgram.run RandomOracle.oracle []).map (fun out => challenge out.result.2) = uniform Bool := by
  simp only [firstProgram, Program.run, RandomOracle.oracle, List.lookup_nil, PMF.map_bind,
    PMF.bind_map, PMF.pure_map, Function.comp_def]
  change sampleBit.bind (fun _ => (uniform (Fin 256)).map challenge) = _
  rw [challenge_uniform, PMF.bind_const]

noncomputable def joint (word : List (Action Bool Bool)) : PMF (PrefixOutcome × InformationState) :=
  (firstProgram.run RandomOracle.oracle []).bind fun out =>
    (run Example.signature Example.policy word (Example.initial (challenge out.result.2))).map fun final => (out, final)

theorem prefix_preserved (word : List (Action Bool Bool)) :
    (joint word).map Prod.fst = firstProgram.run RandomOracle.oracle [] := by
  simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change ((firstProgram.run RandomOracle.oracle []).bind fun out =>
    (run Example.signature Example.policy word (Example.initial (challenge out.result.2))).map (Function.const _ out)) = _
  simp only [PMF.map_const, PMF.bind_pure]

theorem checked_joint (word target : List (Action Bool Bool)) (positions : List Nat)
    (accepted : Certificate.validates Example.signature ∅ word target positions = true) :
    joint word = joint target := by
  unfold joint
  simp_rw [Certificate.validates_kernel Example.signature Example.policy ∅ word target positions accepted]

theorem ordinary_checked_joint (word target : List (Action Bool Bool)) (positions : List Nat)
    (accepted : Certificate.validates Example.signature ∅ word target positions = true) :
    joint word = joint target := by
  rw [Example.validates_eq] at accepted
  unfold joint
  simp_rw [Baseline.validated_kernel Example.signature Example.policy ∅ word target positions accepted]

noncomputable def cost (expensive : Nat) (word : List (Action Bool Bool)) : PMF Nat :=
  (joint word).map (fun pair => Example.finalPrice expensive pair.2)

theorem cost_eq (expensive : Nat) (word : List (Action Bool Bool)) :
    cost expensive word = Example.scheduleCost expensive word := by
  have law := congrArg (fun p => p.bind (fun observed =>
    (run Example.signature Example.policy word (Example.initial observed)).map (Example.finalPrice expensive)))
      first_profile_law
  simpa only [cost, joint, Example.scheduleCost, PMF.map_bind, PMF.map_comp, PMF.bind_map,
    Function.comp_def] using law

theorem late_cost (expensive : Nat) : cost expensive Example.late = PMF.pure 1 := by
  rw [cost_eq, Example.late_cost]

theorem premature_cost (expensive : Nat) : cost expensive Example.premature = priceLaw expensive := by
  rw [cost_eq, Example.premature_cost]

/-- All subsequent computation can inspect the retained prefix and selected
commitments; accepted exchanges preserve this complete continuation law. -/
theorem checked_continuation {Result : Type} (word target : List (Action Bool Bool)) (positions : List Nat)
    (accepted : Certificate.validates Example.signature ∅ word target positions = true)
    (next : PrefixOutcome × InformationState → PMF Result) :
    (joint word).bind next = (joint target).bind next := by
  rw [checked_joint word target positions accepted]

/-- Every schedule can be followed by the actual remaining three calls.
Full game equality alone does not imply a legal visibility exchange. -/
theorem continued_game (word : List (Action Bool Bool)) :
    ((joint word).bind fun pair => continuation pair.1) =
      RandomFunctionMACNativeCaller.target.run RandomOracle.oracle [] := by
  rw [← actual_prefix, Program.run_bind]
  change ((joint word).bind fun pair => continuation pair.1) =
    (firstProgram.run RandomOracle.oracle []).bind continuation
  have law := congrArg (fun p => p.bind continuation) (prefix_preserved word)
  simpa only [PMF.bind_map, Function.comp_def] using law

end Foundation.Symmetric.RandomFunctionMACInformationSchedule
