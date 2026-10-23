import Foundation.Crypto.Logic.Polygraph.GameProofComputational
import Foundation.Constructions.Symmetric.PRGPolygraph

/-! Generated comparison for a real PRG reduction branch. Exact uniform-pad
rewriting and computational replacement retain emitted masking code and its
original execution certificate. The direct compiler omits an identity node;
it is not a new cryptographic assumption or an optimized machine. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.PRGComputational
open Foundation.Probability Foundation.Symmetric
open CryptoLogic.General.Backends
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

inductive Vertex where | half | masked | prg deriving DecidableEq, Repr
inductive Atom where | uniform | replace | direct deriving DecidableEq, Repr

def layout : Layout Vertex Atom Unit Unit where
  source := fun | .uniform | .direct => .half | .replace => .masked
  target := fun | .uniform => .masked | .replace | .direct => .prg
  needs := fun | .uniform | .direct => {()} | .replace => ∅
  charges := fun | .uniform => 0 | .replace | .direct => {()}

def relators (_ : Unit) : Relator layout where
  source := .half
  target := .prg
  left := .seq (.atom Atom.uniform) (.atom Atom.replace)
  right := .atom Atom.direct
  needs := ∅
  balanced := zero_add _

def strategy : Strategy layout .prg where
  rank := fun | .half => 2 | .masked => 1 | .prg => 0
  decreases := by intro label; cases label <;> decide
  terminal := by intro label; cases label <;> decide
  next := fun | .half => .step Atom.uniform | .masked => .step Atom.replace | .prg => .done

def diamonds : {a b c : Vertex} → (first : Transition layout a b) → (second : Transition layout a c) →
    LocalDiamond layout relators first second := by
  intro a b c first second
  rcases first with ⟨one, rfl, rfl⟩
  rcases second with ⟨two, same, rfl⟩
  cases one <;> cases two <;> simp only [layout] at same
  all_goals cases same
  · exact ⟨.masked, .identity _, .identity _, .refl _⟩
  · exact ⟨.prg, .atom Atom.replace, .identity _, .trans (.rule ()) (.symm (.rightUnit _))⟩
  · exact ⟨.prg, .identity _, .identity _, .refl _⟩
  · exact ⟨.prg, .identity _, .atom Atom.replace, .trans (.rightUnit _) (.symm (.rule ()))⟩
  · exact ⟨.prg, .identity _, .identity _, .refl _⟩

def condition (G : Foundation.Symmetric.Generator) (side : Bool) (_ : Unit) : Prop :=
  ∀ n messages observer, Foundation.Symmetric.Generator.Polygraph.halfGap G side n messages observer = Foundation.Symmetric.Generator.Polygraph.maskedGap G side n messages observer

theorem conditions (G : Foundation.Symmetric.Generator) (side : Bool) (needed : Finset Unit) :
    Holds (condition G side) needed := fun _ _ => Foundation.Symmetric.Generator.Polygraph.halfGap_eq G side

noncomputable def object (G : Foundation.Symmetric.Generator) (time : Nat → Nat) (side : Bool) :
    ∀ vertex : Vertex, General.SecurityObject.{0, 0} system
      (match vertex with | .prg => .masking | .half | .masked => .native)
  | .half => Foundation.Symmetric.Generator.Polygraph.object G time (.half side)
  | .masked => Foundation.Symmetric.Generator.Polygraph.object G time (.masked side)
  | .prg => Foundation.Symmetric.Generator.Polygraph.object G time .prg

noncomputable def uniformGiven (G : Foundation.Symmetric.Generator) (time : Nat → Nat) (side : Bool)
    (proof : condition G side ()) : General.CertifiedReduction (object G time side .half) (object G time side .masked) :=
  {Foundation.Symmetric.Generator.Polygraph.uniformRewrite G time side with
    reduction := {
      mapInstance := id
      reduce := fun _ observer => observer
      loss := AdvantageBound.id
      advantage_le := by intro n messages observer; exact (proof n messages observer).le}}

noncomputable def directGiven (G : Foundation.Symmetric.Generator) (time : Nat → Nat) (side : Bool)
    (proof : condition G side ()) : General.CertifiedReduction (object G time side .half) (object G time side .prg) :=
  {(uniformGiven G time side proof).comp (Foundation.Symmetric.Generator.Polygraph.replacement G time side) with
    compiler := .primitive (.mask side)
    code_eq := by intro F A W; rfl}

noncomputable def baseModel (G : Foundation.Symmetric.Generator) (time : Nat → Nat) (side : Bool) :
    Computational.Model system layout (condition G side) where
  machine := fun | .prg => .masking | .half | .masked => .native
  object := object G time side
  atom label proof := match label with
    | .uniform => uniformGiven G time side (proof () (by simp [layout]))
    | .replace => Foundation.Symmetric.Generator.Polygraph.replacement G time side
    | .direct => directGiven G time side (proof () (by simp [layout]))

noncomputable def model (G : Foundation.Symmetric.Generator) (time : Nat → Nat) (side : Bool) :
    Computational.HigherModel system layout relators (condition G side) where
  base := baseModel G time side
  comparison := by
    intro label left right extra
    cases label
    constructor <;> intros <;> rfl

def direct : Plan layout .half .prg := .atom Atom.direct

def generated (plan : Plan layout .half .prg) : Cell layout relators plan direct :=
  terminalCoherence strategy diamonds plan direct

theorem comparison (G : Foundation.Symmetric.Generator) (time : Nat → Nat) (side : Bool)
    (plan : Plan layout .half .prg) :
    General.CertifiedComparison
      (Computational.evaluate (baseModel G time side) plan (conditions G side _))
      (Computational.evaluate (baseModel G time side) direct (conditions G side _)) :=
  Computational.evaluateCell (model G time side) (generated plan) (conditions G side _)

theorem family_eq (G : Foundation.Symmetric.Generator) (time : Nat → Nat) (side : Bool)
    (plan : Plan layout .half .prg) (family) :
    (Computational.evaluate (baseModel G time side) plan (conditions G side _)).reduction.mapFamily family = family :=
  (comparison G time side plan).families family

theorem loss_eq (G : Foundation.Symmetric.Generator) (time : Nat → Nat) (side : Bool)
    (plan : Plan layout .half .prg) (n : Nat) (ε : ℝ≥0∞) :
    (Computational.evaluate (baseModel G time side) plan (conditions G side _)).reduction.loss.eval n ε = ε :=
  (comparison G time side plan).loss n ε

theorem emitted_code (G : Foundation.Symmetric.Generator) (time : Nat → Nat) (side : Bool)
    (plan : Plan layout .half .prg) (program : Machine.Program) :
    (Computational.evaluate (baseModel G time side) plan (conditions G side _)).compiler.run program =
      Machine.Masking.compile side program :=
  (comparison G time side plan).programs program

theorem resources (G : Foundation.Symmetric.Generator) (time : Nat → Nat) (side : Bool)
    (plan : Plan layout .half .prg) (family observer)
    (witness : (object G time side .half).Witness family observer) :
    ((Computational.evaluate (baseModel G time side) plan (conditions G side _)).mapWitness family observer witness).resources =
      () :=
  (comparison G time side plan).resources family observer witness

/-- The backend stores the time profile in the security object, rather than
in its Unit resource field. This theorem exposes the actual stopping bound. -/
theorem halts (G : Foundation.Symmetric.Generator) (time : Nat → Nat) (side : Bool)
    (plan : Plan layout .half .prg) (family observer)
    (witness : (object G time side .half).Witness family observer) (n : Nat)
    (challenge : Bits (G.outputLength n)) :
    Machine.Masking.HaltsWithin (Machine.Masking.compile side witness.code)
      (Machine.Masking.initial (Machine.Masking.compile side witness.code) (G.header n (family n))
        (family n).1.toList (family n).2.toList challenge.toList) (G.reductionTime time n) := by
  have execution := (Computational.evaluate (baseModel G time side) plan (conditions G side _)).toTransform.compiler_executes
    family observer witness
  change (object G time side .prg).execution.ExecutesWithin
    ((Computational.evaluate (baseModel G time side) plan (conditions G side _)).reduction.mapFamily family)
    ((Computational.evaluate (baseModel G time side) plan (conditions G side _)).compiler.run witness.code) _ at execution
  rw [family_eq, emitted_code] at execution
  exact execution n challenge

theorem time_polynomial (G : Foundation.Symmetric.Generator) (time : Nat → Nat)
    (boundedTime : PolynomiallyBounded time) (boundedWidth : PolynomiallyBounded G.outputLength) :
    PolynomiallyBounded (G.reductionTime time) :=
  G.reductionTime_polynomial boundedTime boundedWidth

theorem branch_bound (G : Foundation.Symmetric.Generator) (time : Nat → Nat) (side : Bool)
    (plan : Plan layout .half .prg) (family ε)
    (hypothesis : (object G time side .prg).Bounded family ε) :
    (object G time side .half).Bounded family ε := by
  have target : (object G time side .prg).Bounded
      ((Computational.evaluate (baseModel G time side) plan (conditions G side _)).reduction.mapFamily family) ε := by
    rw [family_eq]
    exact hypothesis
  have result := Computational.bounded (baseModel G time side) plan (conditions G side _) family ε target
  have profile : (fun n => (Computational.evaluate (baseModel G time side) plan (conditions G side _)).reduction.loss.eval n (ε n)) = ε :=
    funext (fun n => loss_eq G time side plan n (ε n))
  rw [profile] at result
  exact result

theorem branch_secure (G : Foundation.Symmetric.Generator) (time : Nat → Nat) (side : Bool)
    (plan : Plan layout .half .prg) (family)
    (hypothesis : (object G time side .prg).Secure family) :
    (object G time side .half).Secure family := by
  apply Computational.secure (baseModel G time side) plan (conditions G side _) family
  rw [family_eq]
  exact hypothesis

/-- The full encryption theorem permits any terminal proof in each branch.
Its two computational hypotheses are applications to the same PRG resource
class, and the final rule is the existing checked triangle inequality. -/
theorem encryption_bound (G : Foundation.Symmetric.Generator) (time : Nat → Nat)
    (leftPlan rightPlan : Plan layout .half .prg) (family ε)
    (hypothesis : (Foundation.Symmetric.Generator.Polygraph.object G time .prg).Bounded family ε) :
    (Foundation.Symmetric.Generator.Polygraph.object G time .encryption).Bounded family (fun n => 2 * ε n) := by
  have first := branch_bound G time false leftPlan family ε hypothesis
  have second := branch_bound G time true rightPlan family ε hypothesis
  intro observer admissible n
  have triangle := (Foundation.Symmetric.Generator.Polygraph.triangle G time).advantage_le family observer n
  exact triangle.trans ((add_le_add (first observer admissible n) (second observer admissible n)).trans_eq (two_mul _).symm)

theorem encryption_secure (G : Foundation.Symmetric.Generator) (time : Nat → Nat)
    (leftPlan rightPlan : Plan layout .half .prg) (family)
    (hypothesis : (Foundation.Symmetric.Generator.Polygraph.object G time .prg).Secure family) :
    (Foundation.Symmetric.Generator.Polygraph.object G time .encryption).Secure family :=
  (Foundation.Symmetric.Generator.Polygraph.triangle G time).secure family
    (branch_secure G time false leftPlan family hypothesis) (branch_secure G time true rightPlan family hypothesis)

/-- A regenerated higher diagram also repairs the computational certificate;
only its declared changed conditions require new proofs. -/
theorem repaired_comparison (G : Foundation.Symmetric.Generator) (time : Nat → Nat) (side : Bool)
    (plan : Plan layout .half .prg) (old : Unit → Prop) (changed : Finset Unit)
    (cached : Holds old ((generated plan).needs layout relators))
    (unchanged : ∀ label ∉ changed, old label → condition G side label)
    (rechecked : Holds (condition G side) ((generated plan).fresh layout relators changed)) :
    let proof := repair cached unchanged rechecked
    General.CertifiedComparison
      (Computational.evaluate (baseModel G time side) plan
        (proof.restrict ((generated plan).endpoint_needs layout relators).1))
      (Computational.evaluate (baseModel G time side) direct
        (proof.restrict ((generated plan).endpoint_needs layout relators).2)) :=
  Computational.repaired_comparison (model G time side) (generated plan) changed cached unchanged rechecked

/-- info: (1, 1) -/
#guard_msgs in
#eval (((generated (strategy.normal .half)).needs layout relators).card,
  ((generated (strategy.normal .half)).fresh layout relators {()}).card)

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.PRGComputational
