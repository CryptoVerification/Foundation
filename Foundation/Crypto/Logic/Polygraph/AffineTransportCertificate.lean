import Foundation.Crypto.Logic.Polygraph.MaskedTransport
import Mathlib.Data.List.FinRange

/-! Proof-generating checks for one precise symbolic fragment. An affine
expression uses constants, inputs, and XOR (= addition in ZMod 2). Testing
zero and the basis vectors is complete, and returns an actual incompatible
root when the test fails. Arbitrary multiplication is kept in a separate
syntax: a complete checker for that syntax would decide formula validity.
These are exact reductions and syntax-node counts, not complexity-class
separations or machine-time claims. -/
namespace CryptoLogic.Polygraph.AffineTransportCertificate

open Foundation.Probability MaskedTransport RootedTransport
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

abbrev Assignment (n : Nat) := Fin n → Bit

/-- Boolean formulas encoded by the field with two elements. Multiplication
is AND, addition is XOR, and 1+e is NOT e. No semantic function is an input. -/
inductive Formula (n : Nat) where
  | constant (value : Bit)
  | input (index : Fin n)
  | add (left right : Formula n)
  | mul (left right : Formula n)

namespace Formula

def eval {n : Nat} : Formula n → Assignment n → Bit
  | .constant value, _ => value
  | .input index, state => state index
  | .add left right, state => left.eval state + right.eval state
  | .mul left right, state => left.eval state * right.eval state

def nodes {n : Nat} : Formula n → Nat
  | .constant _ | .input _ => 1
  | .add left right | .mul left right => left.nodes + right.nodes + 1

/-- Every semantic root assignment is tested by this exhaustive reference
checker. It allows arbitrary sharing in any other checker; no path format
restriction is imposed by the reduction below. -/
def valid? {n : Nat} (formula : Formula n) : Bool := decide (∀ state, formula.eval state = 0)

theorem valid_correct {n : Nat} (formula : Formula n) :
    formula.valid? = true ↔ ∀ state, formula.eval state = 0 := by simp [valid?]

theorem diagram_valid_iff {n : Nat} (formula : Formula n) :
    (∃ joint : PMF (Model.Assignment (State := State (Assignment n))),
      (∀ vertex, joint.map (fun a => a vertex) = law vertex) ∧
      ∀ a ∈ joint.support, (model formula.eval).Compatible a) ↔
    ∀ state, formula.eval state = 0 := MaskedTransport.compatible_joint_iff _

def satisfyingCount {n : Nat} (formula : Formula n) : Nat :=
  (Finset.univ.filter (fun state => formula.eval state ≠ 0)).card

/-- Exact counting transfer, with every distribution-preservation obligation
already discharged by the generated masked diagram. -/
theorem obstruction_count {n : Nat} (formula : Formula n) :
    eventProb (model formula.eval).joint (fun a => ¬(model formula.eval).Compatible a) =
      (formula.satisfyingCount : ℝ≥0∞) * ((2 ^ n : Nat) : ℝ≥0∞)⁻¹ := by
  rw [MaskedTransport.obstruction_probability, uniform_event_count]
  simp [satisfyingCount, Assignment, Bit, ZMod.card]

/-- Any sound and complete decision method for this family of diagrams is
also a decision method for Boolean-formula universal validity. Its internal
proof representation, sharing and auxiliary lemmas are unrestricted. -/
theorem checker_transfer
    (checker : ∀ n, Formula n → Bool)
    (correct : ∀ n (formula : Formula n), checker n formula = true ↔
      ∃ joint : PMF (Model.Assignment (State := State (Assignment n))),
        (∀ vertex, joint.map (fun a => a vertex) = law vertex) ∧
        ∀ a ∈ joint.support, (model formula.eval).Compatible a) :
    ∀ n (formula : Formula n), checker n formula = true ↔
      ∀ state, formula.eval state = 0 := by
  intro n formula
  rw [correct, diagram_valid_iff]

end Formula

/-- The fragment whose semantic side conditions can be discharged by the
generated basis certificate, without a supplied universal equality proof. -/
inductive Affine (n : Nat) where
  | constant (value : Bit)
  | input (index : Fin n)
  | add (left right : Affine n)

namespace Affine

def formula {n : Nat} : Affine n → Formula n
  | .constant value => .constant value
  | .input index => .input index
  | .add left right => .add left.formula right.formula

def eval {n : Nat} (expression : Affine n) : Assignment n → Bit := expression.formula.eval

def constantTerm {n : Nat} : Affine n → Bit
  | .constant value => value
  | .input _ => 0
  | .add left right => left.constantTerm + right.constantTerm

def coefficient {n : Nat} : Affine n → Fin n → Bit
  | .constant _, _ => 0
  | .input index, i => if i = index then 1 else 0
  | .add left right, i => left.coefficient i + right.coefficient i

theorem eval_normal_form {n : Nat} (expression : Affine n) (state : Assignment n) :
    expression.eval state = expression.constantTerm + ∑ i, expression.coefficient i * state i := by
  induction expression with
  | constant value => simp [eval, formula, Formula.eval, constantTerm, coefficient]
  | input index => simp [eval, formula, Formula.eval, constantTerm, coefficient, ite_mul]
  | add left right ihl ihr =>
      change left.eval state + right.eval state = _
      rw [ihl, ihr]
      simp only [constantTerm, coefficient, add_mul, Finset.sum_add_distrib]
      ring

def zero (n : Nat) : Assignment n := fun _ => 0
def basis {n : Nat} (index : Fin n) : Assignment n := fun i => if i = index then 1 else 0

theorem eval_zero {n : Nat} (expression : Affine n) :
    expression.eval (zero n) = expression.constantTerm := by
  simp [eval_normal_form, zero]

theorem eval_basis {n : Nat} (expression : Affine n) (index : Fin n) :
    expression.eval (basis index) = expression.constantTerm + expression.coefficient index := by
  simp [eval_normal_form, basis, mul_ite]

def probes (n : Nat) : List (Assignment n) := zero n :: List.ofFn (@basis n)

theorem probes_length (n : Nat) : (probes n).length = n + 1 := by simp [probes]

theorem basis_complete {n : Nat} (expression : Affine n) :
    (∀ state ∈ probes n, expression.eval state = 0) ↔
      ∀ state, expression.eval state = 0 := by
  constructor
  · intro checked state
    have constant : expression.constantTerm = 0 := by
      simpa only [eval_zero] using checked (zero n) (by simp [probes])
    have coefficients (i : Fin n) : expression.coefficient i = 0 := by
      have h := checked (basis i) (by simp [probes, List.mem_ofFn])
      simpa only [eval_basis, constant, zero_add] using h
    simp [eval_normal_form, constant, coefficients]
  · intro all state _
    exact all state

/-- Failure returns a semantic counterexample, rather than merely `false`. -/
def counterexample {n : Nat} (expression : Affine n) : Option (Assignment n) :=
  (probes n).find? (fun state => decide (expression.eval state ≠ 0))

theorem counterexample_sound {n : Nat} (expression : Affine n) (state : Assignment n)
    (found : expression.counterexample = some state) : expression.eval state ≠ 0 := by
  have h := List.find?_some found
  simpa using h

theorem counterexample_none_iff {n : Nat} (expression : Affine n) :
    expression.counterexample = none ↔ ∀ state, expression.eval state = 0 := by
  rw [counterexample, List.find?_eq_none]
  simpa using expression.basis_complete

theorem diagnosis_correct {n : Nat} (expression : Affine n) :
    expression.counterexample = none ↔
      ∃ joint : PMF (Model.Assignment (State := State (Assignment n))),
        (∀ vertex, joint.map (fun a => a vertex) = law vertex) ∧
        ∀ a ∈ joint.support, (model expression.eval).Compatible a := by
  rw [counterexample_none_iff, MaskedTransport.compatible_joint_iff]

/-- The returned input, with mask zero, is an actual root obstruction in
the generated four-edge graph. Any all-edge realization must fail there. -/
theorem obstruction_certificate {n : Nat} (expression : Affine n) (state : Assignment n)
    (found : expression.counterexample = some state) :
    (model expression.eval).Bad (state, 0) :=
  (MaskedTransport.bad_iff _ _).mpr (expression.counterexample_sound state found)

/-- Actual syntax evaluator with one visit per expression node. No host
state transformer is silently treated as a unit-cost operation here. -/
def evaluateCount {n : Nat} : Affine n → Assignment n → Bit × Nat
  | .constant value, _ => (value, 1)
  | .input index, state => (state index, 1)
  | .add left right, state =>
      let l := left.evaluateCount state
      let r := right.evaluateCount state
      (l.1 + r.1, l.2 + r.2 + 1)

theorem evaluateCount_eq {n : Nat} (expression : Affine n) (state : Assignment n) :
    expression.evaluateCount state = (expression.eval state, expression.formula.nodes) := by
  induction expression with
  | constant value => rfl
  | input index => rfl
  | add left right ihl ihr => simp [evaluateCount, ihl, ihr, eval, formula, Formula.eval, Formula.nodes]

/-- Count all n+1 probes, even when a failed probe permits early exit. This
charges expression payload visits, unlike the earlier certificate-slot count.
Input-coordinate access, bit arithmetic, and list allocation are not native
machine steps; this theorem does not identify these two cost models. -/
def probeVisits {n : Nat} (expression : Affine n) : Nat :=
  ((probes n).map (fun state => (expression.evaluateCount state).2)).sum

theorem probeVisits_eq {n : Nat} (expression : Affine n) :
    expression.probeVisits = (n + 1) * expression.formula.nodes := by
  simp [probeVisits, evaluateCount_eq, List.map_const', List.sum_replicate, probes_length]

/-- Instrument the actual early-exit search, charging every visited node of
the expression payload on every probe that is really evaluated. -/
def searchCount {n : Nat} (expression : Affine n) : List (Assignment n) → Option (Assignment n) × Nat
  | [] => (none, 0)
  | state :: rest =>
      let value := expression.evaluateCount state
      if value.1 = 0 then
        let tail := expression.searchCount rest
        (tail.1, value.2 + tail.2)
      else (some state, value.2)

theorem searchCount_result {n : Nat} (expression : Affine n) (states : List (Assignment n)) :
    (expression.searchCount states).1 =
      states.find? (fun state => decide (expression.eval state ≠ 0)) := by
  induction states with
  | nil => rfl
  | cons state rest ih =>
      simp only [searchCount, evaluateCount_eq]
      by_cases h : expression.eval state = 0 <;> simp [h, ih, List.find?]

theorem searchCount_le {n : Nat} (expression : Affine n) (states : List (Assignment n)) :
    (expression.searchCount states).2 ≤
      (states.map (fun state => (expression.evaluateCount state).2)).sum := by
  induction states with
  | nil => rfl
  | cons state rest ih =>
      simp only [searchCount, evaluateCount_eq, List.map_cons, List.sum_cons]
      split
      · simpa only [evaluateCount_eq] using Nat.add_le_add_left ih expression.formula.nodes
      · exact Nat.le_add_right _ _

theorem checker_visits_le {n : Nat} (expression : Affine n) :
    (expression.searchCount (probes n)).2 ≤ (n + 1) * expression.formula.nodes := by
  calc
    _ ≤ expression.probeVisits := expression.searchCount_le (probes n)
    _ = _ := expression.probeVisits_eq

end Affine
end CryptoLogic.Polygraph.AffineTransportCertificate
