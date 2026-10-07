import Foundation.Logic.Presentation

namespace Foundation.Logic.Examples

set_option backward.isDefEq.respectTransparency false

inductive Rule where
  | closed | triple

abbrev theory : Presentation where
  Judgment := Nat
  Rule := Rule
  arity := fun | .closed => 0 | .triple => 3
  premise := fun _ _ => 0
  conclusion := fun | .closed => 0 | .triple => 1

abbrev context : Context theory := .singleton 0

def proof : Derivation theory context 1 :=
  Derivation.apply (T := theory) Rule.triple (fun _ => .hypothesis 0)

def closed : Derivation theory (Context.empty theory) 0 :=
  Derivation.apply (T := theory) Rule.closed (fun i => Fin.elim0 i)

abbrev numeric : Model theory where
  Carrier := fun _ => Nat
  operation := fun rule children => match rule with
    | .closed => 7
    | .triple => children 0 + children 1 + children 2 + 1

abbrev truth : Model theory where
  Carrier := fun _ => True
  operation := fun rule children => match rule with
    | .closed => True.intro
    | .triple => children 0

/-- info: 7 -/
#guard_msgs in
#eval proof.eval numeric (fun _ => 2)

/-- info: 22 -/
#guard_msgs in
#eval (proof.substitute (fun _ => closed)).eval numeric Fin.elim0

example : (proof.substitute (fun _ => closed)).eval numeric Fin.elim0 =
    proof.eval numeric (fun _ => closed.eval numeric Fin.elim0) :=
  Derivation.eval_substitute numeric Fin.elim0 proof (fun _ => closed)

example : (proof.substitute (fun i => Derivation.hypothesis i)) = proof := proof.substitute_id

example : ∃! _f : Model.Hom (Model.termModel theory (Context.empty theory)) numeric, True :=
  Model.initial theory numeric

-- A variable of judgment 0 cannot be used as a proof of judgment 1.
#check_failure (Derivation.hypothesis (T := theory) (Γ := context) 0 :
  Derivation theory context 1)

end Foundation.Logic.Examples
