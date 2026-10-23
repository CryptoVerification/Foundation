import Foundation.Logic.Polygraph.StructuralTransport
import Foundation.Crypto.Logic.Polygraph.GameProofRequirements
import Foundation.Crypto.Semantics.Probability.Facts

/-! Mixed circuits on finite ports: opaque probabilistic boxes and pure
routing on values already sampled. Tensor feeds each box its own port bundle;
correlations in the incoming bundle are retained. Symbolic charges here are
annotations, not automatically security bounds or native runtime costs. -/
namespace CryptoLogic.Polygraph.MixedCircuit
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
variable {Box Requirement Budget : Type} [DecidableEq Requirement]

structure Signature (Box Requirement Budget : Type) where
  PortAtom : Type
  inputs : Box → Foundation.Logic.Polygraph.StructuralTransport.Shape PortAtom
  outputs : Box → Foundation.Logic.Polygraph.StructuralTransport.Shape PortAtom
  needs : Box → Finset Requirement
  charges : Box → Multiset Budget

abbrev Port (signature : Signature Box Requirement Budget) := Foundation.Logic.Polygraph.StructuralTransport.Shape signature.PortAtom
abbrev Wiring (signature : Signature Box Requirement Budget) := Foundation.Logic.Polygraph.StructuralTransport.Wire (Atom := signature.PortAtom)

inductive Circuit (signature : Signature Box Requirement Budget) : Port signature → Port signature → Type where
  | wire {n m} : Wiring signature n m → Circuit signature n m
  | box (label : Box) : Circuit signature (signature.inputs label) (signature.outputs label)
  | seq {n m k} : Circuit signature n m → Circuit signature m k → Circuit signature n k
  | tensor {n m n' m'} : Circuit signature n m → Circuit signature n' m' → Circuit signature (.pair n n') (.pair m m')

variable {signature : Signature Box Requirement Budget}

def Circuit.needs : {n m : Port signature} → Circuit signature n m → Finset Requirement
  | _, _, .wire _ => ∅
  | _, _, .box label => signature.needs label
  | _, _, .seq first second => first.needs ∪ second.needs
  | _, _, .tensor first second => first.needs ∪ second.needs

def Circuit.charges : {n m : Port signature} → Circuit signature n m → Multiset Budget
  | _, _, .wire _ => 0
  | _, _, .box label => signature.charges label
  | _, _, .seq first second => first.charges + second.charges
  | _, _, .tensor first second => first.charges + second.charges

abbrev Bundle {Atom : Type} (Value : Atom → Type) (n : Foundation.Logic.Polygraph.StructuralTransport.Shape Atom) := n.Value Value

def append {Atom : Type} {Value : Atom → Type} {n m : Foundation.Logic.Polygraph.StructuralTransport.Shape Atom} (first : Bundle Value n) (second : Bundle Value m) : Bundle Value (.pair n m) :=
  (first, second)

structure Model (signature : Signature Box Requirement Budget) (condition : Requirement → Prop) (Value : signature.PortAtom → Type) where
  box : ∀ label, Holds condition (signature.needs label) → Bundle Value (signature.inputs label) →
    PMF (Bundle Value (signature.outputs label))

noncomputable def evaluate {condition : Requirement → Prop} {Value : signature.PortAtom → Type} (model : Model signature condition Value) :
    {n m : Port signature} → (circuit : Circuit signature n m) → Holds condition circuit.needs → Bundle Value n → PMF (Bundle Value m)
  | _, _, .wire wire, _, input => PMF.pure (wire.eval Value input)
  | _, _, .box label, valid, input => model.box label valid input
  | _, _, .seq first second, valid, input =>
      (evaluate model first (valid.restrict Finset.subset_union_left) input).bind
        (evaluate model second (valid.restrict Finset.subset_union_right))
  | _, _, .tensor (n := n) (n' := n') first second, valid, input =>
      (evaluate model first (valid.restrict Finset.subset_union_left) input.1).bind fun left =>
        (evaluate model second (valid.restrict Finset.subset_union_right) input.2).map
          (append left)

/-- Both boundaries and any comparison-only requirements are explicit. -/
structure Relator (signature : Signature Box Requirement Budget) where
  inputs : Port signature
  outputs : Port signature
  left : Circuit signature inputs outputs
  right : Circuit signature inputs outputs
  extra : Finset Requirement
  balanced : left.charges = right.charges

def Relator.support (relator : Relator signature) := relator.left.needs ∪ relator.right.needs ∪ relator.extra

variable {Rule : Type} (relators : Rule → Relator signature)

/-- A catalog root, separated from its placement in a larger circuit. -/
inductive Primitive : {n m : Port signature} → Circuit signature n m → Circuit signature n m → Type where
  | rule (label : Rule) : Primitive (relators label).left (relators label).right

def Primitive.support : {n m : Port signature} → {a b : Circuit signature n m} → Primitive relators a b → Finset Requirement
  | _, _, _, _, .rule label => (relators label).support

/-- A directed local rewrite at one tree position. No arbitrary semantic
equality or whole-circuit normalization is a primitive constructor. -/
inductive Step : {n m : Port signature} → Circuit signature n m → Circuit signature n m → Type where
  | root {n m} {a b : Circuit signature n m} (primitive : Primitive relators a b) : Step a b
  | seqLeft {n m k} {a a' : Circuit signature n m} (change : Step a a') (b : Circuit signature m k) : Step (.seq a b) (.seq a' b)
  | seqRight {n m k} (a : Circuit signature n m) {b b' : Circuit signature m k} (change : Step b b') : Step (.seq a b) (.seq a b')
  | tensorLeft {n m n' m'} {a a' : Circuit signature n m} (change : Step a a') (b : Circuit signature n' m') : Step (.tensor a b) (.tensor a' b)
  | tensorRight {n m n' m'} (a : Circuit signature n m) {b b' : Circuit signature n' m'} (change : Step b b') : Step (.tensor a b) (.tensor a b')

namespace Step
variable {relators}

def support : {n m : Port signature} → {a b : Circuit signature n m} → Step relators a b → Finset Requirement
  | _, _, _, _, .root primitive => primitive.support
  | _, _, _, _, .seqLeft child fixed => child.support ∪ fixed.needs
  | _, _, _, _, .seqRight fixed child => fixed.needs ∪ child.support
  | _, _, _, _, .tensorLeft child fixed => child.support ∪ fixed.needs
  | _, _, _, _, .tensorRight fixed child => fixed.needs ∪ child.support

theorem boundaries {n m} {a b : Circuit signature n m} (change : Step relators a b) :
    a.needs ⊆ change.support ∧ b.needs ⊆ change.support := by
  induction change with
  | root primitive =>
      cases primitive with
      | rule label => exact ⟨fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h),
        fun _ h => Finset.mem_union_left _ (Finset.mem_union_right _ h)⟩
  | seqLeft child fixed ih | tensorLeft child fixed ih =>
      exact ⟨Finset.union_subset_union ih.1 (Finset.Subset.refl _), Finset.union_subset_union ih.2 (Finset.Subset.refl _)⟩
  | seqRight fixed child ih | tensorRight fixed child ih =>
      exact ⟨Finset.union_subset_union (Finset.Subset.refl _) ih.1, Finset.union_subset_union (Finset.Subset.refl _) ih.2⟩

omit [DecidableEq Requirement] in
theorem charge_eq {n m} {a b : Circuit signature n m} (change : Step relators a b) : a.charges = b.charges := by
  induction change with
  | root primitive =>
      cases primitive with
      | rule label => exact (relators label).balanced
  | seqLeft child fixed ih | tensorLeft child fixed ih => exact congrArg (· + fixed.charges) ih
  | seqRight fixed child ih | tensorRight fixed child ih => exact congrArg (fixed.charges + ·) ih

end Step

/-- The model must check every declared local rule under exactly its finite
support. Merely assigning a charge does not prove a cryptographic bound. -/
structure CheckedModel (condition : Requirement → Prop) (Value : signature.PortAtom → Type) where
  base : Model signature condition Value
  localSound : ∀ label (valid : Holds condition (relators label).support) input,
    evaluate base (relators label).left (valid.restrict (by intro x h; exact Finset.mem_union_left _ (Finset.mem_union_left _ h))) input =
    evaluate base (relators label).right (valid.restrict (by intro x h; exact Finset.mem_union_left _ (Finset.mem_union_right _ h))) input

namespace Step
variable {relators}

theorem sound {condition : Requirement → Prop} {Value : signature.PortAtom → Type} (model : CheckedModel relators condition Value)
    {n m} {a b : Circuit signature n m} (change : Step relators a b) (valid : Holds condition change.support)
    (left : Holds condition a.needs) (right : Holds condition b.needs) (input : Bundle Value n) :
    evaluate model.base a left input = evaluate model.base b right input := by
  induction change with
  | root primitive =>
      cases primitive with
      | rule label => exact model.localSound label valid input
  | seqLeft child fixed ih =>
      simp only [evaluate]
      exact congrArg (fun (law : PMF (Bundle Value _)) => law.bind (evaluate model.base fixed _))
        (ih (valid.restrict Finset.subset_union_left) _ _ input)
  | seqRight fixed child ih =>
      apply congrArg (fun continuation => (evaluate model.base fixed _ input).bind continuation)
      funext middle
      exact ih (valid.restrict Finset.subset_union_right) _ _ middle
  | tensorLeft child fixed ih =>
      simp only [evaluate]
      exact congrArg (fun (law : PMF (Bundle Value _)) => law.bind (fun first => (evaluate model.base fixed _ _).map (append first)))
        (ih (valid.restrict Finset.subset_union_left) _ _ _)
  | tensorRight fixed child ih =>
      apply congrArg (fun continuation => (evaluate model.base fixed _ _).bind continuation)
      funext first
      exact congrArg (PMF.map (append first)) (ih (valid.restrict Finset.subset_union_right) _ _ _)

/-- Retain an arbitrary correlated prior context AND the original input in
the output law. The theorem does not replace shared state by independent runs. -/
theorem sound_joint {condition : Requirement → Prop} {Value : signature.PortAtom → Type} {Context : Type} (model : CheckedModel relators condition Value)
    {n m} {a b : Circuit signature n m} (change : Step relators a b) (valid : Holds condition change.support)
    (left : Holds condition a.needs) (right : Holds condition b.needs) (law : PMF (Context × Bundle Value n)) :
    law.bind (fun past => (evaluate model.base a left past.2).map (fun next => (past, next))) =
      law.bind (fun past => (evaluate model.base b right past.2).map (fun next => (past, next))) := by
  apply congrArg (fun continuation => law.bind continuation)
  funext past
  rw [change.sound model valid left right past.2]

theorem repaired {old updated : Requirement → Prop} {Value : signature.PortAtom → Type} (model : CheckedModel relators updated Value)
    {n m} {a b : Circuit signature n m} (change : Step relators a b) (changed : Finset Requirement)
    (cached : Holds old change.support) (unchanged : ∀ label ∉ changed, old label → updated label)
    (rechecked : Holds updated (fresh change.support changed)) (input : Bundle Value n) :
    let valid := repair cached unchanged rechecked
    evaluate model.base a (valid.restrict change.boundaries.1) input =
      evaluate model.base b (valid.restrict change.boundaries.2) input :=
  change.sound model (repair cached unchanged rechecked) _ _ input

end Step
end CryptoLogic.Polygraph.MixedCircuit
