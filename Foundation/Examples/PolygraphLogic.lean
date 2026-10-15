import Foundation.Logic.Polygraph.Interpretation
import Foundation.Logic.Polygraph.Occurrences

/-! Executable and negative examples of the logical diagram interface. All
rules and models here are synthetic; no cryptographic claim is assumed. -/
namespace Foundation.Logic.Polygraph.Examples

set_option backward.isDefEq.respectTransparency false

inductive Rule where
  | closed | unary | alternative | binary | triple

abbrev theory : Logic.Presentation where
  Judgment := Nat
  Rule := Rule
  arity := fun | .closed => 0 | .unary | .alternative => 1 | .binary => 2 | .triple => 3
  premise := fun _ _ => 0
  conclusion := fun _ => 0

abbrev one : Logic.Context theory := .singleton 0
abbrev two : Logic.Context theory := ⟨2, fun _ => 0⟩

abbrev numeric : Logic.Model theory where
  Carrier := fun _ => Nat
  operation := fun rule children => match rule with
    | .closed => 7
    | .unary => children 0 + 1
    | .alternative => children 0 + 2
    | .binary => children 0 + children 1
    | .triple => children 0 + children 1 + children 2

abbrev truth : Logic.Model theory where
  Carrier := fun _ => True
  operation := fun _ _ => True.intro

def duplicate : Diagram theory one two := .wiring ⟨fun _ => 0, fun _ => rfl⟩

def shared : Diagram theory one one := .seq duplicate (Diagram.generator (T := theory) Rule.binary)

/-- info: 6 -/
#guard_msgs in
#eval shared.eval numeric (fun _ => 3) 0

/-- info: [0, 0] -/
#guard_msgs in
#eval shared.occurrences.map Fin.val

example : shared.toDerivation =
    Logic.Derivation.apply (T := theory) .binary (fun _ => .hypothesis (Γ := one) 0) := rfl

example : shared.eval truth (fun _ => True.intro) 0 = True.intro := rfl

def closed : Diagram theory (Logic.Context.empty theory) one :=
  Diagram.ofDerivation (Logic.Derivation.apply (T := theory) (Γ := Logic.Context.empty theory)
    Rule.closed (fun i => Fin.elim0 i))

/-- info: 7 -/
#guard_msgs in
#eval closed.eval numeric Fin.elim0 0

def tripleProof : Logic.Derivation theory one 0 :=
  Logic.Derivation.apply (T := theory) Rule.triple (fun _ => .hypothesis 0)

/-- info: 9 -/
#guard_msgs in
#eval (Diagram.ofDerivation tripleProof).eval numeric (fun _ => 3) 0

example : (Diagram.ofDerivation tripleProof).toDerivation = tripleProof :=
  Diagram.toDerivation_ofDerivation tripleProof

example : (tripleProof.substitute (fun _ => closed.toDerivation)).occurrences = [] := rfl

example (replacement : ∀ i, Logic.Derivation theory one (one.claim i)) :
    (tripleProof.substitute replacement).occurrences =
      tripleProof.occurrences.flatMap (fun i => (replacement i).occurrences) :=
  Logic.Derivation.occurrences_substitute tripleProof replacement

def swap : Diagram theory two two := .wiring ⟨Fin.rev, fun _ => rfl⟩

/-- info: [8, 3] -/
#guard_msgs in
#eval List.ofFn (swap.eval numeric (Fin.cases 3 (fun _ => 8)))

def independent : Diagram theory (Context.append one one) (Context.append one one) :=
  .tensor (Diagram.generator (T := theory) Rule.unary) (Diagram.generator (T := theory) Rule.alternative)

/-- info: [4, 10] -/
#guard_msgs in
#eval List.ofFn (independent.eval numeric (Fin.cases 3 (fun _ => 8)))

example : (Diagram.wiring (Wiring.discard one)).occurrences = [] := rfl

example (f : Forest one two) : (Diagram.ofForest f).toForest = f :=
  Diagram.toForest_ofForest f

/-- Parallel boundaries alone do not force the same interpreted value. -/
example : (Diagram.generator (T := theory) .unary).eval numeric (fun _ => 3) 0 ≠
    (Diagram.generator (T := theory) .alternative).eval numeric (fun _ => 3) 0 := by decide

-- A one-element context cannot supply a three-premise boundary.
#guard_msgs (drop info) in
#check_failure (Diagram.seq (Diagram.identity one) (Diagram.generator (T := theory) .triple))

-- A position with judgment 0 cannot be wired to an output with judgment 1.
#guard_msgs (drop info) in
#check_failure (Wiring.mk (Γ := one) (Δ := Logic.Context.singleton (T := theory) 1)
  (fun _ => 0) (fun _ => rfl))

end Foundation.Logic.Polygraph.Examples
