import Foundation.Constructions.Symmetric.PRGNativeQueryResources
import Foundation.Crypto.Logic.General.NativeSingleChallengeBackend
import Foundation.Crypto.Logic.General.ConstrainedObservedExecution
import Foundation.Crypto.Logic.General.CertifiedObservedExecution

/-! Register the public-input PRG reductions with genuine termination, one
query and complete encoded memory bounds. Context faithfulness fixes both
the reply law and the public message branch; it admits no hidden advice. -/
namespace Foundation.Symmetric.PRGNativeQueryBackend
open Machine Foundation.Probability TimedExecution CryptoLogic.General ContractObservedBackend
open NativeSingleChallengeBackend
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

noncomputable def modelGame (G : Generator) (F : InstanceFamily G.prgGoal)
    (A : AdversaryFamily G.prgGoal F) (n : Nat) (world : Bool) : PMF Bool :=
  (if world then G.ideal n else G.real n).bind (A n)

theorem advantage_eq (G : Generator) (F : InstanceFamily G.prgGoal)
    (A : AdversaryFamily G.prgGoal F) (n : Nat) :
    advantageProfile G.prgGoal F A n =
      probabilityGap (eventProb (modelGame G F A n false) (· = true))
        (eventProb (modelGame G F A n true) (· = true)) := rfl

noncomputable def baseRegistration (G : Generator) :=
  Counted.registration runtime event (modelGame G) (advantage_eq G)

def FaithfulContext (G : Generator) (F : InstanceFamily G.prgGoal) (r : Profile G.prgGoal runtime) : Prop :=
  ∃ branch : Bool, ∀ n world, r.context n (F n) world =
    ⟨PRGNativeQueryExecution.publicInput G n (G.message (F n) branch),
      (if world then G.ideal n else G.real n).map Bits.toList⟩

noncomputable def registration (G : Generator) :=
  ((baseRegistration G).restrict (fun F _ resources => FaithfulContext G F resources.1)).certify
    (Nat → Nat) (fun F code resources cap => resources.1.WithinPeak runtime measure cap F code)

variable (G : Generator) (O : PolynomialObserver) (branch : Bool)

noncomputable def adversary (F : InstanceFamily G.prgGoal) : AdversaryFamily G.prgGoal F :=
  fun n => G.reduce (F n) branch (PRGNativePad.observer O)

noncomputable def profile : Profile G.prgGoal runtime where
  context := fun n messages world =>
    ⟨PRGNativeQueryExecution.publicInput G n (G.message messages branch),
      (if world then G.ideal n else G.real n).map Bits.toList⟩
  horizon := PRGNativeQueryExecution.timeBound G O
  logicalGame := fun _ n messages world =>
    (if world then G.ideal n else G.real n).bind (G.reduce messages branch (PRGNativePad.observer O))

variable (F : InstanceFamily G.prgGoal) (hWidth : PolynomiallyBounded G.outputLength)

include hWidth in
theorem executes : (profile G O branch).ExecutesWithin runtime F (PRGNativeReductionConcrete.fixedCode O) := by
  refine ⟨PRGNativeQueryExecution.time_polynomial G hWidth O, ?_⟩
  intro n world
  let distribution := if world then G.ideal n else G.real n
  let message := G.message (F n) branch
  let Q := PRGNativeQueryExecution.component O
  let C := NativeSingleChallenge.Execution.completion distribution Bits.toList
    (PRGNativeQueryExecution.publicInput G n message) Q (PRGNativeQueryExecution.adapt G n message)
    (PRGNativeQueryExecution.entry G O n message) (G.outputLength n) (PRGNativeReductionConcrete.timeBound G O n)
    (fun _ _ => by simp) (fun reply _ => PRGNativeQueryExecution.consumer_budget G hWidth O n message reply)
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C, NativeSingleChallenge.Execution.completion]
    rw [Completion.ofProcedure_budget]
    rw [NativeSingleChallenge.Execution.whole_budget, PRGNativeQueryExecution.timeBound_eq]
    exact Nat.le_refl _
  · have hRun := C.final_run (NativeSingleChallenge.absorbing (distribution.map Bits.toList) Q.procedure.code)
      (PRGNativeQueryExecution.timeBound G O n) (by
        dsimp only [C, NativeSingleChallenge.Execution.completion]
        rw [Completion.ofProcedure_budget]
        rw [NativeSingleChallenge.Execution.whole_budget, PRGNativeQueryExecution.timeBound_eq])
    rw [← hRun]
    exact PRGNativeQueryExecution.run_game G hWidth O n (F n) branch distribution _ (Nat.le_refl _)

theorem one_query : Counted.WithinEvents runtime event (profile G O branch) (fun _ => 1)
    F (PRGNativeReductionConcrete.fixedCode O) := by
  refine ⟨PolynomiallyBounded.const 1, ?_⟩
  intro n world elapsed _ target ht
  exact NativeSingleChallenge.at_most_one_query
    ((if world then G.ideal n else G.real n).map Bits.toList) _
    (PRGNativeQueryExecution.publicInput G n (G.message (F n) branch)) elapsed target ht

include hWidth in
theorem peak : (profile G O branch).WithinPeak runtime measure (PRGNativeQueryExecution.bitBound G O)
    F (PRGNativeReductionConcrete.fixedCode O) := by
  refine ⟨PRGNativeQueryExecution.space_polynomial G O hWidth, ?_⟩
  intro n world elapsed he target ht
  exact PRGNativeQueryExecution.storage_peak G O n (G.message (F n) branch)
    (if world then G.ideal n else G.real n) elapsed he target ht

include hWidth in
noncomputable def witness : (registration G).object.Witness F (adversary G O branch F) :=
  ((baseRegistration G).restrict (fun F _ resources => FaithfulContext G F resources.1)).certifyWitness
    (Nat → Nat) (fun F code resources cap => resources.1.WithinPeak runtime measure cap F code)
    F (adversary G O branch F)
    ((baseRegistration G).restrictWitness (fun F _ resources => FaithfulContext G F resources.1)
      F (adversary G O branch F)
      (Counted.witness runtime event (modelGame G) (advantage_eq G) F (adversary G O branch F)
        (PRGNativeReductionConcrete.fixedCode O) (profile G O branch) (fun _ => 1)
        (executes G O branch F hWidth) (one_query G O branch F) (fun _ _ => rfl))
      ⟨branch, fun _ _ => rfl⟩)
    (PRGNativeQueryExecution.bitBound G O) (peak G O branch F hWidth)

include hWidth in
theorem witness_code : (witness G O branch F hWidth).code = PRGNativeReductionConcrete.fixedCode O := rfl

include hWidth in
theorem witness_queries : (witness G O branch F hWidth).resources.1.2 = (fun _ => 1) := rfl

include hWidth in
theorem witness_peak : (witness G O branch F hWidth).resources.1.1.WithinPeak runtime measure
    (witness G O branch F hWidth).resources.2 F (witness G O branch F hWidth).code :=
  (witness G O branch F hWidth).executes.2

include hWidth in
theorem witness_advantage (n : Nat) :
    (registration G).nativeAdvantage F (witness G O branch F hWidth).code
      (witness G O branch F hWidth).resources n =
    G.prgGoal.advantage n (F n) (G.reduce (F n) branch (PRGNativePad.observer O)) :=
  ((registration G).realizes_advantage F (adversary G O branch F) _ _
    (witness G O branch F hWidth).realizes n).symm

end Foundation.Symmetric.PRGNativeQueryBackend
