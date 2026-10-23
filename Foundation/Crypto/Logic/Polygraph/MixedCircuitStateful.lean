import Foundation.Crypto.Logic.Polygraph.MixedCircuit

/-! Evaluation of the original mixed syntax with one explicitly threaded state.
Tensor runs its left child and then its right child on the resulting state.
Pure wires copy/discard port values, never the implicit shared state. Local
soundness is universal in that state; arbitrary effectful interchange is not
assumed. The state may contain a transcript, but no automatic native runtime
contract or log-preservation law is inferred from this evaluator. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Stateful
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
variable {Box Requirement Budget State : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget}

structure Model (signature : Signature Box Requirement Budget) (condition : Requirement → Prop)
    (Value : signature.PortAtom → Type) (State : Type) where
  box : ∀ label, Holds condition (signature.needs label) → State → Bundle Value (signature.inputs label) →
    PMF (State × Bundle Value (signature.outputs label))

noncomputable def evaluate {condition : Requirement → Prop} {Value : signature.PortAtom → Type}
    (model : Model signature condition Value State) :
    {n m : Port signature} → (circuit : Circuit signature n m) → Holds condition circuit.needs →
      State → Bundle Value n → PMF (State × Bundle Value m)
  | _, _, .wire wire, _, state, input => PMF.pure (state, wire.eval Value input)
  | _, _, .box label, valid, state, input => model.box label valid state input
  | _, _, .seq first second, valid, state, input =>
      (evaluate model first (valid.restrict Finset.subset_union_left) state input).bind fun middle =>
        evaluate model second (valid.restrict Finset.subset_union_right) middle.1 middle.2
  | _, _, .tensor first second, valid, state, input =>
      (evaluate model first (valid.restrict Finset.subset_union_left) state input.1).bind fun left =>
        (evaluate model second (valid.restrict Finset.subset_union_right) left.1 input.2).map fun right =>
          (right.1, (left.2, right.2))

/-- A state-independent old model embeds without changing any port law. -/
noncomputable def lift {condition : Requirement → Prop} {Value : signature.PortAtom → Type}
    (model : MixedCircuit.Model signature condition Value) : Model signature condition Value State where
  box label valid state input := (model.box label valid input).map fun output => (state, output)

theorem evaluate_lift {condition : Requirement → Prop} {Value : signature.PortAtom → Type}
    (model : MixedCircuit.Model signature condition Value) {n m} (circuit : Circuit signature n m)
    (valid : Holds condition circuit.needs) (state : State) (input : Bundle Value n) :
    evaluate (lift model) circuit valid state input =
      (MixedCircuit.evaluate model circuit valid input).map (fun output => (state, output)) := by
  induction circuit generalizing state with
  | wire wire => simp only [evaluate, MixedCircuit.evaluate, PMF.pure_map]
  | box label => rfl
  | seq first second ihFirst ihSecond =>
      simp only [evaluate, MixedCircuit.evaluate, ihFirst, PMF.bind_map, Function.comp_def, ihSecond, PMF.map_bind]
  | tensor first second ihFirst ihSecond =>
      simp only [evaluate, MixedCircuit.evaluate, ihFirst, PMF.bind_map, Function.comp_def, ihSecond,
        PMF.map_bind, PMF.map_comp, append]

structure CheckedModel (relators : Rule → Relator signature) (condition : Requirement → Prop)
    (Value : signature.PortAtom → Type) (State : Type) where
  base : Model signature condition Value State
  localSound : ∀ label (valid : Holds condition (relators label).support) state input,
    evaluate base (relators label).left
      (valid.restrict (by intro x h; exact Finset.mem_union_left _ (Finset.mem_union_left _ h))) state input =
    evaluate base (relators label).right
      (valid.restrict (by intro x h; exact Finset.mem_union_left _ (Finset.mem_union_right _ h))) state input

variable {Rule : Type} {relators : Rule → Relator signature}

/-- Existing checked state-independent roots remain checked after lifting. -/
noncomputable def liftChecked {condition : Requirement → Prop} {Value : signature.PortAtom → Type}
    (model : MixedCircuit.CheckedModel relators condition Value) : CheckedModel relators condition Value State where
  base := lift model.base
  localSound label valid state input := by
    simp only [evaluate_lift]
    rw [model.localSound label valid input]

theorem sound {condition : Requirement → Prop} {Value : signature.PortAtom → Type}
    (model : CheckedModel relators condition Value State) {n m} {a b : Circuit signature n m}
    (change : Step relators a b) (valid : Holds condition change.support)
    (left : Holds condition a.needs) (right : Holds condition b.needs) (state : State) (input : Bundle Value n) :
    evaluate model.base a left state input = evaluate model.base b right state input := by
  induction change generalizing state with
  | root primitive => cases primitive with
    | rule label => exact model.localSound label valid state input
  | seqLeft child fixed ih =>
      simp only [evaluate]
      exact congrArg (fun (law : PMF (State × Bundle Value _)) => law.bind (fun middle => evaluate model.base fixed _ middle.1 middle.2))
        (ih (valid.restrict Finset.subset_union_left) _ _ state input)
  | seqRight fixed child ih =>
      apply congrArg (fun continuation => (evaluate model.base fixed _ state input).bind continuation)
      funext middle
      exact ih (valid.restrict Finset.subset_union_right) _ _ middle.1 middle.2
  | tensorLeft child fixed ih =>
      simp only [evaluate]
      exact congrArg (fun (law : PMF (State × Bundle Value _)) => law.bind (fun first =>
        (evaluate model.base fixed _ first.1 input.2).map (fun second => (second.1, (first.2, second.2)))))
        (ih (valid.restrict Finset.subset_union_left) _ _ state input.1)
  | tensorRight fixed child ih =>
      apply congrArg (fun continuation => (evaluate model.base fixed _ state input.1).bind continuation)
      funext first
      exact congrArg (PMF.map (fun second => (second.1, (first.2, second.2))))
        (ih (valid.restrict Finset.subset_union_right) _ _ first.1 input.2)

/-- Preserve correlated past, original state and original port input. -/
theorem sound_joint {condition : Requirement → Prop} {Value : signature.PortAtom → Type} {Context : Type}
    (model : CheckedModel relators condition Value State) {n m} {a b : Circuit signature n m}
    (change : Step relators a b) (valid : Holds condition change.support)
    (left : Holds condition a.needs) (right : Holds condition b.needs)
    (law : PMF (Context × (State × Bundle Value n))) :
    law.bind (fun past => (evaluate model.base a left past.2.1 past.2.2).map (fun next => (past, next))) =
      law.bind (fun past => (evaluate model.base b right past.2.1 past.2.2).map (fun next => (past, next))) := by
  apply congrArg (fun continuation => law.bind continuation)
  funext past
  rw [sound model change valid left right past.2.1 past.2.2]

theorem repaired {old updated : Requirement → Prop} {Value : signature.PortAtom → Type}
    (model : CheckedModel relators updated Value State) {n m} {a b : Circuit signature n m}
    (change : Step relators a b) (changed : Finset Requirement)
    (cached : Holds old change.support) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh change.support changed)) (state : State) (input : Bundle Value n) :
    let valid := repair cached unchanged rechecked
    evaluate model.base a (valid.restrict change.boundaries.1) state input =
      evaluate model.base b (valid.restrict change.boundaries.2) state input :=
  sound model change (repair cached unchanged rechecked) _ _ state input

end CryptoLogic.Polygraph.MixedCircuit.Stateful
