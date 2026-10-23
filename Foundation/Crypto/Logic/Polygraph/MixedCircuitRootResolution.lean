import Foundation.Crypto.Logic.Polygraph.MixedCircuitBranching
import Foundation.Logic.Polygraph.Rewriting

/-! Resolve all local branchings when primitive redexes are rigid: a rewrite
inside a primitive source must be that same primitive rewrite. This explicit
root contract is stronger than general critical-pair confluence. It does not
assume comparisons for arbitrary parallel paths. -/
namespace CryptoLogic.Polygraph.MixedCircuit
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open Foundation.Logic.Polygraph
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}

/-- No distinct concurrent rewrite occurs at or within a primitive redex. -/
def RootRigid (relators : Rule → Relator signature) : Prop :=
  ∀ {n m} {a b : Circuit signature n m} (primitive : Primitive relators a b)
    {c : Circuit signature n m} (other : Step relators a c), c = b ∧ HEq other (Step.root primitive)

inductive Resolution {n m} {a b c : Circuit signature n m} (first : Step relators a b) (second : Step relators a c) where
  | same (destinations : b = c) (edges : HEq first second)
  | separate (witness : Separated first second)

namespace Resolution

def seqLeft {n m k} {a b c : Circuit signature n m} {s : Step relators a b} {t : Step relators a c}
    (result : Resolution s t) (fixed : Circuit signature m k) : Resolution (.seqLeft s fixed) (.seqLeft t fixed) :=
  match result with
  | .same destinations edges => .same (congrArg (fun x => Circuit.seq x fixed) destinations)
      (by cases destinations; cases eq_of_heq edges; rfl)
  | .separate witness => .separate (.seqLeft witness fixed)

def seqRight {n m k} (fixed : Circuit signature n m) {a b c : Circuit signature m k}
    {s : Step relators a b} {t : Step relators a c} (result : Resolution s t) : Resolution (.seqRight fixed s) (.seqRight fixed t) :=
  match result with
  | .same destinations edges => .same (congrArg (Circuit.seq fixed) destinations)
      (by cases destinations; cases eq_of_heq edges; rfl)
  | .separate witness => .separate (.seqRight fixed witness)

def tensorLeft {n m n' m'} {a b c : Circuit signature n m} {s : Step relators a b} {t : Step relators a c}
    (result : Resolution s t) (fixed : Circuit signature n' m') : Resolution (.tensorLeft s fixed) (.tensorLeft t fixed) :=
  match result with
  | .same destinations edges => .same (congrArg (fun x => Circuit.tensor x fixed) destinations)
      (by cases destinations; cases eq_of_heq edges; rfl)
  | .separate witness => .separate (.tensorLeft witness fixed)

def tensorRight {n m n' m'} (fixed : Circuit signature n m) {a b c : Circuit signature n' m'}
    {s : Step relators a b} {t : Step relators a c} (result : Resolution s t) : Resolution (.tensorRight fixed s) (.tensorRight fixed t) :=
  match result with
  | .same destinations edges => .same (congrArg (Circuit.tensor fixed) destinations)
      (by cases destinations; cases eq_of_heq edges; rfl)
  | .separate witness => .separate (.tensorRight fixed witness)

end Resolution

/-- Executable recursion on actual steps. Rigid root branches agree;
separated branches use only the previous split squares and context lifting. -/
def Step.resolve (rigid : RootRigid relators) : {n m : Port signature} → {a b c : Circuit signature n m} →
    (first : Step relators a b) → (second : Step relators a c) → Resolution first second
  | _, _, _, _, _, .root primitive, second => .same (rigid primitive second).1.symm (rigid primitive second).2.symm
  | _, _, _, _, _, first, .root primitive => .same (rigid primitive first).1 (rigid primitive first).2
  | _, _, _, _, _, .seqLeft first fixed, .seqLeft second _ => (first.resolve rigid second).seqLeft fixed
  | _, _, _, _, _, .seqLeft first _, .seqRight _ second => .separate (.seqLR first second)
  | _, _, _, _, _, .seqRight _ first, .seqLeft second _ => .separate (.seqRL second first)
  | _, _, _, _, _, .seqRight fixed first, .seqRight _ second => .seqRight fixed (first.resolve rigid second)
  | _, _, _, _, _, .tensorLeft first fixed, .tensorLeft second _ => (first.resolve rigid second).tensorLeft fixed
  | _, _, _, _, _, .tensorLeft first _, .tensorRight _ second => .separate (.tensorLR first second)
  | _, _, _, _, _, .tensorRight _ first, .tensorLeft second _ => .separate (.tensorRL second first)
  | _, _, _, _, _, .tensorRight fixed first, .tensorRight _ second => .tensorRight fixed (first.resolve rigid second)

abbrev Path {n m} (a b : Circuit signature n m) := RewritePath (fun x y => Step relators x y) a b

namespace Path

def support {n m : Port signature} : {a b : Circuit signature n m} → Path (relators := relators) a b → Finset Requirement
  | _, _, .refl a => a.needs
  | _, _, .cons change tail => change.support ∪ support tail

theorem boundaries {n m} {a b : Circuit signature n m} (path : Path (relators := relators) a b) :
    a.needs ⊆ support path ∧ b.needs ⊆ support path := by
  induction path with
  | refl => simp only [support]; exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | cons change tail ih =>
      simp only [support]
      exact ⟨fun _ h => Finset.mem_union_left _ (change.boundaries.1 h),
        fun _ h => Finset.mem_union_right _ (ih.2 h)⟩

theorem single_support {n m} {a b : Circuit signature n m} (change : Step relators a b) :
    support (RewritePath.single change) = change.support := by
  simpa only [RewritePath.single, support] using Finset.union_eq_left.mpr change.boundaries.2

omit [DecidableEq Requirement] in
theorem charge_eq {n m} {a b : Circuit signature n m} (path : Path (relators := relators) a b) : a.charges = b.charges := by
  induction path with
  | refl => rfl
  | cons change tail ih => exact change.charge_eq.trans ih

theorem sound {condition : Requirement → Prop} {Value : signature.PortAtom → Type}
    (model : CheckedModel relators condition Value) {n m} {a b : Circuit signature n m}
    (path : Path (relators := relators) a b) (valid : Holds condition (support path))
    (left : Holds condition a.needs) (right : Holds condition b.needs) (input : Bundle Value n) :
    evaluate model.base a left input = evaluate model.base b right input := by
  induction path with
  | refl => rfl
  | cons change tail ih =>
      simp only [support] at valid
      let middle := (valid.restrict Finset.subset_union_left).restrict change.boundaries.2
      exact (change.sound model (valid.restrict Finset.subset_union_left) left middle input).trans
        (ih (valid.restrict Finset.subset_union_right) middle right)

theorem sound_joint {condition : Requirement → Prop} {Value : signature.PortAtom → Type} {Context : Type}
    (model : CheckedModel relators condition Value) {n m} {a b : Circuit signature n m}
    (path : Path (relators := relators) a b) (valid : Holds condition (support path))
    (left : Holds condition a.needs) (right : Holds condition b.needs) (law : PMF (Context × Bundle Value n)) :
    law.bind (fun past => (evaluate model.base a left past.2).map (fun next => (past, next))) =
      law.bind (fun past => (evaluate model.base b right past.2).map (fun next => (past, next))) := by
  apply congrArg (fun continuation => law.bind continuation)
  funext past
  rw [path.sound model valid left right past.2]

end Path

/-- Zero- or one-step residual routes, with certified finite guard coverage. -/
structure LocalJoin {n m} {a b c : Circuit signature n m} (first : Step relators a b) (second : Step relators a c) where
  target : Circuit signature n m
  afterFirst : Path (relators := relators) b target
  afterSecond : Path (relators := relators) c target
  covered : Path.support afterFirst ⊆ first.support ∪ second.support ∧
    Path.support afterSecond ⊆ first.support ∪ second.support

def Resolution.join {n m} {a b c : Circuit signature n m} {first : Step relators a b} {second : Step relators a c}
    (result : Resolution first second) : LocalJoin first second :=
  match result with
  | .same destinations _ => by
      cases destinations
      refine ⟨b, .refl b, .refl b, ?_⟩
      simp only [Path.support]
      exact ⟨fun _ h => Finset.mem_union_left _ (first.boundaries.2 h),
        fun _ h => Finset.mem_union_left _ (first.boundaries.2 h)⟩
  | .separate witness =>
      ⟨witness.diamond.target, RewritePath.single witness.diamond.afterFirst, RewritePath.single witness.diamond.afterSecond,
        by simpa only [Path.single_support] using witness.no_new_conditions⟩

def Step.localJoin (rigid : RootRigid relators) {n m} {a b c : Circuit signature n m}
    (first : Step relators a b) (second : Step relators a c) : LocalJoin first second :=
  (first.resolve rigid second).join

theorem Resolution.join_length {n m} {a b c : Circuit signature n m} {first : Step relators a b} {second : Step relators a c}
    (result : Resolution first second) :
    result.join.afterFirst.length ≤ 1 ∧ result.join.afterSecond.length ≤ 1 := by
  cases result with
  | same destinations edges => cases destinations; simp [join, RewritePath.length]
  | separate witness => simp [join, RewritePath.single, RewritePath.length]

end CryptoLogic.Polygraph.MixedCircuit
