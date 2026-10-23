import Foundation.Crypto.Logic.General.ResourceImprovement
import Foundation.Logic.Polygraph.RelationalInterpretation
import Foundation.Crypto.Logic.General.Backends

/-! A native finite-code optimization with exact 2-to-1 transition traces.
The cryptographic goal is deliberately synthetic; its role is to exercise
real stopping/distribution certificates, not claim a new encryption result.
Also tests the missing-monotonicity and irreversible-improvement boundaries. -/
namespace CryptoLogic.General.ResourceImprovement.Examples
open Foundation.Probability
open Implementation
set_option backward.isDefEq.respectTransparency false

abbrev fast : Machine.Program := [.halt]
abbrev slow : Machine.Program := [.jump 1, .halt]

theorem fast_trace (input : List Bool) : Machine.HaltsWith fast input [] 1 := by
  refine ⟨{ Machine.Configuration.initial input with halted := true }, ?_, rfl, rfl⟩
  exact .succ (.zero _) (.halt rfl rfl)

theorem slow_trace (input : List Bool) : Machine.HaltsWith slow input [] 2 := by
  refine ⟨{ Machine.Configuration.initial input with pc := 1, halted := true }, ?_, rfl, rfl⟩
  refine .succ (d := { Machine.Configuration.initial input with pc := 1 })
    (.succ (.zero _) ?_) (.halt rfl rfl)
  simp [Machine.Step, Machine.successors, Machine.next, Machine.Instruction.next,
    Machine.Configuration.initial]

theorem fast_law (input : List Bool) : Machine.evalWithin fast input 1 = PMF.pure (some []) :=
  (fast_trace input).evalWithin_eq_pure_of_no_randomBit (by intro tape; simp [fast])

theorem slow_law (input : List Bool) : Machine.evalWithin slow input 2 = PMF.pure (some []) :=
  (slow_trace input).evalWithin_eq_pure_of_no_randomBit (by intro tape; simp [slow])

theorem slow_never_one (input : List Bool) : ¬ Machine.HaltsWithin slow input 1 := by
  intro h
  have state := h { Machine.Configuration.initial input with pc := 1 }
    (.succ (.zero _) (Or.inl (by simp [Machine.Step, Machine.successors, Machine.next,
      Machine.Instruction.next, Machine.Configuration.initial])))
  contradiction

def goal : CryptoGoal where
  Instance := fun _ => Unit
  Adversary := fun _ _ => Unit
  advantage := fun _ _ _ => 0

def object : SecurityObject.{0, 0} Backends.system .native where
  goal := goal
  execution := {
    Resources := Nat → Nat
    ExecutesWithin := fun _ code budget => PolynomiallyBounded budget ∧
      ∀ input, Machine.HaltsWithin code input (budget input.length)
    Realizes := fun _ _ code budget => ∀ input,
      Machine.evalWithin code input (budget input.length) = PMF.pure (some []) }
  adversaries := ⟨fun _ _ => True⟩
  represented := by
    intro F A _
    exact ⟨fast, fun _ => 1, ⟨PolynomiallyBounded.const 1, Machine.haltInstruction_haltsWithin⟩,
      fast_law⟩

instance : PartialOrder object.execution.Resources :=
  inferInstanceAs (PartialOrder (Nat → Nat))

def fastWitness (F A) : object.Witness F A :=
  ⟨fast, fun _ => 1, ⟨PolynomiallyBounded.const 1, Machine.haltInstruction_haltsWithin⟩,
    fast_law, True.intro⟩

def slowWitness (F A) : object.Witness F A :=
  ⟨slow, fun _ => 2, ⟨PolynomiallyBounded.const 2, fun input =>
    (slow_trace input).haltsWithin_of_no_randomBit (by intro tape; simp [slow])⟩,
    slow_law, True.intro⟩

def optimized : Implementation object object (identitySemantic object) where
  compiler := .primitive (.native (.constant fast))
  mapWitness := fun F A _ => fastWitness F A
  code_eq := by intros; rfl

def original : Implementation object object (identitySemantic object) where
  compiler := .primitive (.native (.constant slow))
  mapWitness := fun F A _ => slowWitness F A
  code_eq := by intros; rfl

theorem improves : Improves optimized original := by
  intro F A W size
  exact Nat.le_succ 1

theorem not_reverse : ¬ Improves original optimized := by
  intro h
  have bad := h (fun _ => ()) (fun _ => ()) (fastWitness _ _) 0
  change (2 : Nat) ≤ 1 at bad
  exact (by decide : ¬ (2 : Nat) ≤ 1) bad

theorem optimized_monotone : MonotoneResources optimized := by
  intro F A W W' _
  exact le_rfl

/-- Actual emitted finite code differs; resources and all stopping proofs
belong to each code separately. -/
theorem code_changed (F A) (W : object.Witness F A) :
    optimized.compiler.run W.code ≠ original.compiler.run W.code := by
  change fast ≠ slow
  decide

def threeWitness (F A) : object.Witness F A :=
  ⟨fast, fun _ => 3, ⟨PolynomiallyBounded.const 3, fun input => by
    apply Machine.haltsWithin_of_no_timeout_support
    have same := Machine.evalWithin_stable fast input 1 2 (Machine.haltInstruction_haltsWithin input)
    rw [same, fast_law]
    simp⟩, fun input => by
      have same := Machine.evalWithin_stable fast input 1 2 (Machine.haltInstruction_haltsWithin input)
      rw [same, fast_law], True.intro⟩

/-- A fully certified suffix can select nonmonotone upper bounds. It still
emits a real program, halts, and realizes the same adversary at every input. -/
def nonmonotoneSuffix : Implementation object object (identitySemantic object) where
  compiler := .primitive (.native (.constant fast))
  mapWitness := fun F A W => if W.resources 0 = 1 then threeWitness F A else fastWitness F A
  code_eq := by intro F A W; split <;> rfl

theorem postcompose_fails : ¬ Improves (optimized.comp nonmonotoneSuffix)
    (original.comp nonmonotoneSuffix) := by
  intro h
  have bad := h (fun _ => ()) (fun _ => ()) (fastWitness _ _) 0
  change (3 : Nat) ≤ 1 at bad
  exact (by decide : ¬ (3 : Nat) ≤ 1) bad

theorem suffix_not_monotone : ¬ MonotoneResources nonmonotoneSuffix := by
  intro h
  exact postcompose_fails (postcompose improves nonmonotoneSuffix h)

/-- The valid monotone suffix composes with an actual strict optimization. -/
theorem optimized_chain : Improves (optimized.comp optimized) (original.comp optimized) :=
  postcompose improves optimized optimized_monotone

/-- The same quantitative loss certificate applies to the changed code. -/
def certifiedOptimized : CertifiedReduction object object :=
  optimized.certifyReduction (Reduction.id object.goal) AdvantageBound.id_preservesNegligible

theorem optimized_security (F) (h : object.Secure F) : object.Secure F :=
  certifiedOptimized.secure F h

/-- The optimized emitted program satisfies a strictly tighter target class. -/
def tight : Implementation object (object.refine (fun _ _ r => ∀ n, r n ≤ 1))
    (identitySemantic object) := optimized.constrain (fun r => ∀ n, r n ≤ 1)
      (fun _ _ _ _ => le_rfl)

theorem tight_code (F A) (W : object.Witness F A) :
    (tight.mapWitness F A W).code = fast := rfl

theorem tight_bound (F A) (W : object.Witness F A) :
    ∀ n, (tight.mapWitness F A W).resources n ≤ 1 := (tight.mapWitness F A W).executes.2

namespace Diagrams
open Foundation.Logic Foundation.Logic.Polygraph

abbrev theory : Presentation where
  Judgment := Unit
  Rule := Unit
  arity := fun _ => 1
  premise := fun _ _ => ()
  conclusion := fun _ => ()

abbrev Endomorphism := Implementation object object (identitySemantic object)

def better : Model theory where
  Carrier := fun _ => Endomorphism
  operation := fun _ children => (children 0).comp optimized

def worse : Model theory where
  Carrier := fun _ => Endomorphism
  operation := fun _ children => (children 0).comp original

def related : InterpretationRelation better worse where
  Rel := fun _ => Improves
  rule := by
    intro rule left right h
    exact comp_improves (h 0) improves optimized_monotone

/-- The local certificate above yields resource improvement for every full
inference diagram, not just for a bounded list of tested compositions. -/
theorem all_diagrams {Γ Δ : Foundation.Logic.Context theory} (d : Diagram theory Γ Δ)
    (left : Environment better Γ) (right : Environment worse Γ)
    (h : ∀ i, Improves (left i) (right i)) (i : Fin Δ.length) :
    Improves (d.eval better left i) (d.eval worse right i) :=
  related.diagram d left right h i

abbrev one : Foundation.Logic.Context theory := Foundation.Logic.Context.singleton ()
def parallel : Diagram theory (Foundation.Logic.Polygraph.Context.append one one) (Foundation.Logic.Polygraph.Context.append one one) :=
  .tensor (.generator ()) (.generator ())

/-- info: 1 -/
#guard_msgs in
#eval ((parallel.eval better (fun _ => Implementation.identity object) 0).compiler.run fast).length

/-- info: 2 -/
#guard_msgs in
#eval ((parallel.eval worse (fun _ => Implementation.identity object) 0).compiler.run fast).length

example : Improves (parallel.eval better (fun _ => Implementation.identity object) 0)
    (parallel.eval worse (fun _ => Implementation.identity object) 0) :=
  all_diagrams _ _ _ (fun _ => improves_refl _) 0

def firstRoute : Diagram.Cell3 (.seq (.identity _) parallel) parallel := .step (.leftUnit parallel)
def secondRoute : Diagram.Cell3 (.seq (.identity _) parallel) parallel :=
  Diagram.connect _ _ firstRoute.forest_eq

def routeComparison : Cartesian.Cell4 firstRoute secondRoute := Cartesian.coherent _ _

theorem reordered_optimization (i : Fin 2) :
    Improves (parallel.eval better (fun _ => Implementation.identity object) i)
      (parallel.eval worse (fun _ => Implementation.identity object) i) :=
  related.structural firstRoute secondRoute _ _ (fun _ => improves_refl _) i

end Diagrams

end CryptoLogic.General.ResourceImprovement.Examples
