import Foundation.Crypto.Logic.Polygraph.MixedCircuitStatefulWiringUnion

/-! A controlled pass over every pure-wire leaf of a mixed circuit. The pass
preserves the circuit skeleton and never moves copy/discard across an effectful
box. Its witness uses the actual eighteen-law wiring presentation. This is a
preprocessing retraction, not higher coherence or completion of the union. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Stateful.WiringUnion.WirePass
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {original : Rule → Relator signature}
set_option backward.isDefEq.respectTransparency false

def output : {a b : Port signature} → Circuit signature a b → Circuit signature a b
  | _, _, .wire wire => .wire (Cartesian.reify (TypedRouting.normal wire))
  | _, _, .box label => .box label
  | _, _, .seq first second => .seq (output first) (output second)
  | _, _, .tensor first second => .tensor (output first) (output second)

theorem output_needs {a b} (circuit : Circuit signature a b) :
    (output circuit).needs = circuit.needs := by
  induction circuit <;> simp_all only [output, Circuit.needs]

omit [DecidableEq Requirement] in
theorem output_charges {a b} (circuit : Circuit signature a b) :
    (output circuit).charges = circuit.charges := by
  induction circuit <;> simp_all only [output, Circuit.charges]

omit [DecidableEq Requirement] in
theorem output_idempotent {a b} (circuit : Circuit signature a b) :
    output (output circuit) = output circuit := by
  induction circuit with
  | wire wire => simp only [output, Cartesian.reify_normal]
  | box => rfl
  | seq first second one two => simp only [output, one, two]
  | tensor first second one two => simp only [output, one, two]

def boxes : {a b : Port signature} → Circuit signature a b → Multiset Box
  | _, _, .wire _ => 0
  | _, _, .box label => {label}
  | _, _, .seq first second | _, _, .tensor first second => boxes first + boxes second

omit [DecidableEq Requirement] in
theorem output_boxes {a b} (circuit : Circuit signature a b) :
    boxes (output circuit) = boxes circuit := by
  induction circuit <;> simp_all only [output, boxes]

def witness : {a b : Port signature} → (circuit : Circuit signature a b) →
    RewriteTrack (relators := rules original) circuit (output circuit)
  | _, _, .wire wire => normalize wire
  | _, _, .box label => .refl (Circuit.box (signature := signature) label)
  | _, _, .seq first second =>
      .comp ((Placement.seqLeft second).track (witness first))
        ((Placement.seqRight (output first)).track (witness second))
  | _, _, .tensor first second =>
      .comp ((Placement.tensorLeft second).track (witness first))
        ((Placement.tensorRight (output first)).track (witness second))

theorem witness_support {a b} (circuit : Circuit signature a b) :
    RewriteTrack.support (witness (original := original) circuit) = circuit.needs := by
  induction circuit with
  | wire wire => exact normalize_support wire
  | box => rfl
  | seq first second one two | tensor first second one two =>
      simp only [witness, RewriteTrack.support, Placement.track_support, Placement.needs,
        one, two, output_needs, Circuit.needs, Finset.union_self, Finset.union_comm]

omit [DecidableEq Requirement] in
/-- Every pure leaf rewrite is erased by the pass as an equality of syntax.
This is not a higher comparison between the original proof tracks. -/
theorem wire_step_output {a b} {p q : Wiring signature a b} (change : Cartesian.Step p q) :
    output (Circuit.wire p) = output (Circuit.wire q) := by
  have same : TypedRouting.normal p = TypedRouting.normal q :=
    (TypedRouting.normal_complete p q).mpr change.sound
  exact congrArg (fun layout => Circuit.wire (Cartesian.reify layout)) same

omit [DecidableEq Requirement] in
theorem wire_step_output_in_context {a b c d} {p q : Wiring signature a b}
    (change : Cartesian.Step p q) (place : Placement (signature := signature) a b c d) :
    output (place.apply (.wire p)) = output (place.apply (.wire q)) := by
  cases place with
  | seqLeft fixed => exact congrArg (fun child => Circuit.seq child (output fixed)) (wire_step_output change)
  | seqRight fixed => exact congrArg (Circuit.seq (output fixed)) (wire_step_output change)
  | tensorLeft fixed => exact congrArg (fun child => Circuit.tensor child (output fixed)) (wire_step_output change)
  | tensorRight fixed => exact congrArg (Circuit.tensor (output fixed)) (wire_step_output change)

omit [DecidableEq Requirement] in
/-- The earlier all-steps-decrease interface cannot be instantiated for the
full union. A chosen terminating pass must not be advertised as that interface. -/
theorem no_all_steps_strategy : ¬ Nonempty (Strategy (rules original)) := by
  rintro ⟨strategy⟩
  let shape : Port signature := .unit
  let chain (n : Nat) : Circuit signature shape (.pair shape shape) :=
    .wire (Cartesian.copyChain shape n)
  have falling (n : Nat) : strategy.rank (chain (n + 1)) < strategy.rank (chain n) :=
    strategy.decreases (wireStep (Cartesian.copyChainStep shape n))
  have bounded (n : Nat) : strategy.rank (chain n) + n ≤ strategy.rank (chain 0) := by
    induction n with
    | zero => omega
    | succ n ih => have decrease := falling n; omega
  have impossible := bounded (strategy.rank (chain 0) + 1)
  omega

theorem sound {State : Type} {condition : Requirement → Prop} {Value : signature.PortAtom → Type}
    (model : CheckedModel original condition Value State) {a b} (circuit : Circuit signature a b)
    (valid : Holds condition circuit.needs) (right : Holds condition (output circuit).needs)
    (state : State) (input : Bundle Value a) :
    evaluate model.base circuit valid state input = evaluate model.base (output circuit) right state input := by
  have covered : Holds condition (RewriteTrack.support (witness (original := original) circuit)) := by
    rw [witness_support]
    exact valid
  exact track_sound (checked model) (witness circuit) covered valid right state input

/-- Correlated past data, initial shared state and input remain in the joint
law. Only the already sampled data is copied by pure-wire leaves. -/
theorem repaired_joint {State Context : Type} {old updated : Requirement → Prop}
    {Value : signature.PortAtom → Type} (model : CheckedModel original updated Value State)
    {a b} (circuit : Circuit signature a b) (changed : Finset Requirement)
    (cached : Holds old circuit.needs) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh circuit.needs changed))
    (law : Foundation.Probability.ProbComp (Context × (State × Bundle Value a))) :
    ∃ left : Holds updated circuit.needs, ∃ right : Holds updated (output circuit).needs,
      law.bind (fun past => (evaluate model.base circuit left past.2.1 past.2.2).map (fun next => (past, next))) =
        law.bind (fun past => (evaluate model.base (output circuit) right past.2.1 past.2.2).map (fun next => (past, next))) := by
  let valid := repair cached unchanged rechecked
  have right : Holds updated (output circuit).needs := by rw [output_needs]; exact valid
  refine ⟨valid, right, ?_⟩
  congr 1
  funext past
  rw [sound model circuit valid right past.2.1 past.2.2]

end CryptoLogic.Polygraph.MixedCircuit.Stateful.WiringUnion.WirePass
