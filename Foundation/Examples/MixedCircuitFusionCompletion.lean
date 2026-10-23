import Foundation.Examples.MixedCircuitFusionObstruction

/-! Conservative completion of association against sequential wire fusion.
Old rules are embedded unchanged. The new suffix fusion expands to inverse
association followed by old fusion. Global confluence is not asserted. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural.Fusion
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
set_option backward.isDefEq.respectTransparency false

inductive Rule where
  | existing (label : Structural.Rule true)
  | suffix {a b c d : Port signature} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d)

def rules : Rule → Relator signature
  | .existing label => Structural.rules label
  | .suffix p q tail => ⟨_, _, .seq (.wire p) (.seq (.wire q) tail), .seq (.wire (.seq p q)) tail,
      ∅, by simp [Circuit.charges]⟩

def embedPrimitive {a b} {p q : Circuit signature a b} (change : Primitive (@Structural.rules true) p q) :
    Primitive rules p q := by
  cases change with
  | rule label => exact Primitive.rule (relators := rules) (Rule.existing label)

def embedStep : {a b : Port signature} → {p q : Circuit signature a b} →
    Step (@Structural.rules true) p q → Step rules p q
  | _, _, _, _, .root change => .root (embedPrimitive change)
  | _, _, _, _, .seqLeft change fixed => .seqLeft (embedStep change) fixed
  | _, _, _, _, .seqRight fixed change => .seqRight fixed (embedStep change)
  | _, _, _, _, .tensorLeft change fixed => .tensorLeft (embedStep change) fixed
  | _, _, _, _, .tensorRight fixed change => .tensorRight fixed (embedStep change)

def embedTrack {a b : Port signature} : {p q : Circuit signature a b} →
    RewriteTrack (relators := @Structural.rules true) p q → RewriteTrack (relators := rules) p q
  | _, _, .refl p => .refl p
  | _, _, .step change => .step (embedStep change)
  | _, _, .comp first second => .comp (embedTrack first) (embedTrack second)
  | _, _, .inv child => .inv (embedTrack child)

def embedPath {a b : Port signature} : {p q : Circuit signature a b} →
    Path (relators := @Structural.rules true) p q → Path (relators := rules) p q
  | _, _, .refl p => .refl p
  | _, _, .cons change tail => .cons (embedStep change) (embedPath tail)

theorem embedPrimitive_support {a b} {p q : Circuit signature a b} (change : Primitive (@Structural.rules true) p q) :
    (embedPrimitive change).support = change.support := by
  cases change
  rfl

theorem embedStep_support {a b} {p q : Circuit signature a b} (change : Step (@Structural.rules true) p q) :
    (embedStep change).support = change.support := by
  induction change <;> simp_all only [embedStep, Step.support, embedPrimitive_support]

theorem embedTrack_support {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := @Structural.rules true) p q) :
    RewriteTrack.support (embedTrack path) = RewriteTrack.support path := by
  induction path <;> simp_all only [embedTrack, RewriteTrack.support, embedStep_support]

theorem embedPath_support {a b} {p q : Circuit signature a b} (path : Path (relators := @Structural.rules true) p q) :
    Path.support (embedPath path) = Path.support path := by
  induction path <;> simp_all only [embedPath, Path.support, embedStep_support]

def suffixStep {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
    Step rules (.seq (.wire p) (.seq (.wire q) tail)) (.seq (.wire (.seq p q)) tail) :=
  .root (.rule (relators := rules) (Rule.suffix p q tail))

def expandPrimitive {a b} {p q : Circuit signature a b} (change : Primitive rules p q) :
    RewriteTrack (relators := @Structural.rules true) p q := by
  cases change with
  | rule label =>
      cases label with
      | existing label => exact .step (.root (.rule label))
      | suffix p q tail =>
          exact .comp (.inv (.step (associate (.wire p) (.wire q) tail))) (.step (.seqLeft (seqFusion p q) tail))

def expandStep : {a b : Port signature} → {p q : Circuit signature a b} →
    Step rules p q → RewriteTrack (relators := @Structural.rules true) p q
  | _, _, _, _, .root change => expandPrimitive change
  | _, _, _, _, .seqLeft change fixed => (Placement.seqLeft fixed).track (expandStep change)
  | _, _, _, _, .seqRight fixed change => (Placement.seqRight fixed).track (expandStep change)
  | _, _, _, _, .tensorLeft change fixed => (Placement.tensorLeft fixed).track (expandStep change)
  | _, _, _, _, .tensorRight fixed change => (Placement.tensorRight fixed).track (expandStep change)

def expandTrack {a b : Port signature} : {p q : Circuit signature a b} →
    RewriteTrack (relators := rules) p q → RewriteTrack (relators := @Structural.rules true) p q
  | _, _, .refl p => .refl p
  | _, _, .step change => expandStep change
  | _, _, .comp first second => .comp (expandTrack first) (expandTrack second)
  | _, _, .inv child => .inv (expandTrack child)

theorem expandPrimitive_support {a b} {p q : Circuit signature a b} (change : Primitive rules p q) :
    RewriteTrack.support (expandPrimitive change) = change.support := by
  cases change with
  | rule label =>
      cases label with
      | existing label => rfl
      | suffix p q tail =>
          simp [expandPrimitive, associate, seqFusion, RewriteTrack.support, Step.support,
            Primitive.support, Relator.support, rules, Structural.rules, Circuit.needs]

theorem expandStep_support {a b} {p q : Circuit signature a b} (change : Step rules p q) :
    RewriteTrack.support (expandStep change) = change.support := by
  induction change with
  | root change => exact expandPrimitive_support change
  | seqLeft change fixed ih | seqRight fixed change ih | tensorLeft change fixed ih | tensorRight fixed change ih =>
      simp only [expandStep, Placement.track_support, ih, Placement.needs, Step.support] <;>
        exact Finset.union_comm _ _

theorem expandTrack_support {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := rules) p q) :
    RewriteTrack.support (expandTrack path) = RewriteTrack.support path := by
  induction path <;> simp_all only [expandTrack, RewriteTrack.support, expandStep_support]

theorem embedTrack_placement {a b c d} (place : Placement (signature := signature) a b c d)
    {p q : Circuit signature a b} (path : RewriteTrack (relators := @Structural.rules true) p q) :
    embedTrack (place.track path) = place.track (embedTrack path) := by
  cases place <;> induction path <;> simp_all only [Placement.track, Placement.apply, Track.map, embedTrack, embedStep, Placement.step]

theorem expandTrack_placement {a b c d} (place : Placement (signature := signature) a b c d)
    {p q : Circuit signature a b} (path : RewriteTrack (relators := rules) p q) :
    expandTrack (place.track path) = place.track (expandTrack path) := by
  cases place <;> induction path <;> simp_all only [Placement.track, Placement.apply, Track.map, expandTrack, expandStep, Placement.step]

theorem expand_embedStep {a b} {p q : Circuit signature a b} (change : Step (@Structural.rules true) p q) :
    expandStep (embedStep change) = Track.step change := by
  induction change with
  | root change => cases change; rfl
  | seqLeft change fixed ih | seqRight fixed change ih | tensorLeft change fixed ih | tensorRight fixed change ih =>
      simp only [embedStep, expandStep, ih, Placement.track, Track.map, Placement.step]

theorem expand_embedTrack {a b} {p q : Circuit signature a b} (path : RewriteTrack (relators := @Structural.rules true) p q) :
    expandTrack (embedTrack path) = path := by
  induction path <;> simp_all only [embedTrack, expandTrack, expand_embedStep]

/-- Every old checked interpretation extends with the same base kernels. -/
noncomputable def extendModel {condition : Nat → Prop} {Value : signature.PortAtom → Type}
    (checked : CheckedModel (@Structural.rules true) condition Value) : CheckedModel rules condition Value where
  base := checked.base
  localSound := by
    intro label valid input
    let change := Primitive.rule (relators := rules) label
    have expanded : Holds condition (RewriteTrack.support (expandPrimitive change)) := by
      rw [expandPrimitive_support]
      exact valid
    exact RewriteTrack.sound checked (expandPrimitive change) expanded _ _ input

theorem suffixStep_support {a b c d} (p : Wiring signature a b) (q : Wiring signature b c) (tail : Circuit signature c d) :
    (suffixStep p q tail).support = tail.needs := by
  simp [suffixStep, Step.support, Primitive.support, Relator.support, rules, Circuit.needs]

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural.Fusion
