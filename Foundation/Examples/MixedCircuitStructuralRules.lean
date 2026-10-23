import Foundation.Examples.MixedCircuitMACHigher
import Foundation.Logic.Polygraph.StructuralWireRewrite

/-! Actual wire edits, wire/circuit fusion, general circuit association and
MAC contraction share one rule catalogue. The optional suffix rule is a local
completion of the association/MAC peak. Global convergence and completeness
of this catalogue are not asserted. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
open Foundation.Probability
open Foundation.Logic.Polygraph
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open Foundation.Logic.Polygraph.ScheduleCertificate
set_option backward.isDefEq.respectTransparency false
abbrev WireEdit {a b : Port signature} (p q : Wiring signature a b) := Foundation.Logic.Polygraph.StructuralTransport.Rewrite.Step p q

inductive Rule (completed : Bool) where
  | crypto (stage : Nat)
  | assoc {a b c d : Port signature} (p : Circuit signature a b) (q : Circuit signature b c) (r : Circuit signature c d)
  | wire {a b : Port signature} {p q : Wiring signature a b} (change : WireEdit p q)
  | fuseSeq {a b c : Port signature} (p : Wiring signature a b) (q : Wiring signature b c)
  | fuseTensor {a b c d : Port signature} (p : Wiring signature a b) (q : Wiring signature c d)
  | suffix (enabled : completed = true) (stage : Nat) {target : Port signature} (tail : Circuit signature finish target)

def rules {completed : Bool} : Rule completed → Relator signature
  | .crypto stage => MAC.relators stage
  | .assoc p q r => ⟨_, _, .seq (.seq p q) r, .seq p (.seq q r), ∅, add_assoc _ _ _⟩
  | .wire (p := p) (q := q) _ => ⟨_, _, .wire p, .wire q, ∅, rfl⟩
  | .fuseSeq p q => ⟨_, _, .seq (.wire p) (.wire q), .wire (.seq p q), ∅, by simp [Circuit.charges]⟩
  | .fuseTensor p q => ⟨_, _, .tensor (.wire p) (.wire q), .wire (.tensor p q), ∅, by simp [Circuit.charges]⟩
  | .suffix _ stage tail =>
      ⟨_, _, .seq (.box (MACNormalization.Atom.schedule stage)) (.seq (.box (MACNormalization.Atom.eliminate stage)) tail),
        .seq (after stage) tail, ∅, by simp [after, Circuit.charges, signature, MACNormalization.layout]⟩

noncomputable def model (orders : Nat → Schedule 8) (completed : Bool) :
    CheckedModel (@rules completed) (MACNormalization.condition orders) (family orders) where
  base := base orders
  localSound := by
    intro label valid input
    cases label with
    | crypto stage => exact (MAC.model orders).localSound stage valid input
    | assoc p q r => simp only [rules, evaluate, PMF.bind_bind]
    | wire change =>
        exact congrArg PMF.pure (change.sound (family orders) input)
    | fuseSeq p q =>
        simp only [rules, evaluate, PMF.pure_bind]
        rfl
    | fuseTensor p q =>
        simp only [rules, evaluate, PMF.pure_bind, PMF.pure_map]
        rfl
    | suffix enabled stage tail =>
        simp only [rules, after, evaluate, base_schedule, base_eliminate, PMF.pure_bind]

inductive Profile where
  | wire (composite : Bool)
  | schedule (stage : Nat)
  | eliminate (stage : Nat)
  | seq (left right : Profile)
  | tensor (left right : Profile)
  deriving DecidableEq, Repr

def profile : {a b : Port signature} → Circuit signature a b → Profile
  | _, _, .wire p => .wire (Foundation.Logic.Polygraph.StructuralTransport.Rewrite.composite p)
  | _, _, .box (.schedule stage) => .schedule stage
  | _, _, .box (.eliminate stage) => .eliminate stage
  | _, _, .seq left right => .seq (profile left) (profile right)
  | _, _, .tensor left right => .tensor (profile left) (profile right)

/-- Over-approximation only: arbitrary composite pure wires are flagged.
The false result is sufficient to prove irreducibility of the fork endpoints. -/
def rootCandidate (completed : Bool) : Profile → Bool
  | .wire compound => compound
  | .seq (.seq _ _) _ => true
  | .seq (.wire _) (.wire _) | .tensor (.wire _) (.wire _) => true
  | .seq (.schedule stage) (.eliminate other) => decide (stage = other)
  | .seq (.schedule stage) (.seq (.eliminate other) _) => completed && decide (stage = other)
  | _ => false

def candidates (completed : Bool) : {a b : Port signature} → Circuit signature a b → Nat
  | _, _, .wire p => if Foundation.Logic.Polygraph.StructuralTransport.Rewrite.composite p then 1 else 0
  | _, _, .box _ => 0
  | _, _, .seq left right => (if rootCandidate completed (.seq (profile left) (profile right)) then 1 else 0) + candidates completed left + candidates completed right
  | _, _, .tensor left right => (if rootCandidate completed (.tensor (profile left) (profile right)) then 1 else 0) + candidates completed left + candidates completed right

theorem primitive_candidate {completed : Bool} {a b} {p q : Circuit signature a b}
    (change : Primitive (@rules completed) p q) : 0 < candidates completed p := by
  cases change with
  | rule label =>
      cases label with
      | crypto stage => simp [rules, MAC.relators, candidates, rootCandidate, profile, before]
      | assoc p q r => simp [rules, candidates, rootCandidate, profile]
      | wire change => simp [rules, candidates, change.source_composite]
      | fuseSeq p q | fuseTensor p q => simp [rules, candidates, rootCandidate, profile]
      | suffix enabled stage tail =>
          cases enabled
          simp [rules, candidates, rootCandidate, profile]

theorem step_candidate {completed : Bool} {a b} {p q : Circuit signature a b}
    (change : Step (@rules completed) p q) : 0 < candidates completed p := by
  induction change with
  | root root => exact primitive_candidate root
  | seqLeft child fixed ih | seqRight fixed child ih | tensorLeft child fixed ih | tensorRight fixed child ih =>
      simp only [candidates]
      omega

theorem stopped_of_no_candidates {completed : Bool} {a b} {p : Circuit signature a b}
    (empty : candidates completed p = 0) {q} (change : Step (@rules completed) p q) : False := by
  have positive := step_candidate change
  omega

def forkSource (stage : Nat) {target : Port signature} (wire : Wiring signature finish target) := Circuit.seq (before stage) (.wire wire)
def forkDirect (stage : Nat) {target : Port signature} (wire : Wiring signature finish target) := Circuit.seq (after stage) (.wire wire)
def forkAssociated (stage : Nat) {target : Port signature} (wire : Wiring signature finish target) :=
  Circuit.seq (.box (signature := signature) (MACNormalization.Atom.schedule stage))
    (.seq (.box (MACNormalization.Atom.eliminate stage)) (.wire wire))

def cryptoFirst (completed : Bool) (stage : Nat) {target} (wire : Wiring signature finish target) :
    Step (@rules completed) (forkSource stage wire) (forkDirect stage wire) :=
  .seqLeft (.root (.rule (relators := @rules completed) (Rule.crypto stage))) _

def assocFirst (completed : Bool) (stage : Nat) {target} (wire : Wiring signature finish target) :
    Step (@rules completed) (forkSource stage wire) (forkAssociated stage wire) :=
  .root (.rule (relators := @rules completed) (Rule.assoc _ _ _))

def completedResidual (stage : Nat) {target} (wire : Wiring signature finish target) :
    Step (@rules true) (forkAssociated stage wire) (forkDirect stage wire) :=
  .root (.rule (relators := @rules true) (Rule.suffix rfl stage (.wire wire)))

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural
