import Foundation.Crypto.Logic.Polygraph.MixedCircuitBranching
import Foundation.Examples.GameProofMACNormalization

/-! A kernel-level bridge to the actual MAC preparation/elimination paths.
Port atoms retain the original game vertices. Full state and trace survive
sampled-value copy/drop comparisons. This step does not reprove security
bounds for arbitrary mixed diagrams or compile new native programs. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open Foundation.Logic.Polygraph.ScheduleCertificate
set_option backward.isDefEq.respectTransparency false
abbrev Outcome := CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC.FullOutcome

def signature : Signature MACNormalization.Atom Nat Unit where
  PortAtom := MACNormalization.Vertex
  inputs label := .atom (MACNormalization.layout.source label)
  outputs label := .atom (MACNormalization.layout.target label)
  needs := MACNormalization.layout.needs
  charges := MACNormalization.layout.charges

def source (stage : Nat) : Port signature := .atom (.stage stage)
def finish : Port signature := .atom .finish

noncomputable def family (orders : Nat → Schedule 8) (vertex : signature.PortAtom) : Type :=
  (MACNormalization.game orders vertex).Outcome

theorem wrong_game_connection (stage other : Nat) :
    signature.outputs (.eliminate stage) ≠ signature.inputs (.schedule other) := by
  intro impossible
  cases impossible

def before (stage : Nat) : Circuit signature (source (stage + 1)) finish :=
  .seq (.box (signature := signature) (MACNormalization.Atom.schedule stage)) (.box (signature := signature) (MACNormalization.Atom.eliminate stage))

def after (stage : Nat) : Circuit signature (source (stage + 1)) finish := .box (signature := signature) (MACNormalization.Atom.eliminate (stage + 1))

def relators (stage : Nat) : Relator signature where
  inputs := source (stage + 1)
  outputs := finish
  left := before stage
  right := after stage
  extra := ∅
  balanced := by simp [before, after, Circuit.charges, signature, MACNormalization.layout]

def rewrite (stage : Nat) : Step relators (before stage) (after stage) := .root (.rule stage)

noncomputable def base (orders : Nat → Schedule 8) : Model signature (MACNormalization.condition orders) (family orders) where
  box label valid input := ((MACNormalization.baseModel orders).atom label valid).kernel input

theorem base_schedule (orders : Nat → Schedule 8) (stage : Nat)
    (valid : Holds (MACNormalization.condition orders) (signature.needs (.schedule stage))) (input : Outcome) :
    (base orders).box (signature := signature) (MACNormalization.Atom.schedule stage) valid input = PMF.pure input :=
  CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC.schedule_kernel _ _ input

theorem base_eliminate (orders : Nat → Schedule 8) (stage : Nat)
    (valid : Holds (MACNormalization.condition orders) (signature.needs (.eliminate stage))) (input : Outcome) :
    (base orders).box (signature := signature) (MACNormalization.Atom.eliminate stage) valid input = PMF.pure (MACNormalization.sanitize input) := rfl

/-- These are the original conditional state kernels, not merely the same
success probability or a replacement attack with a shorter transcript. -/
theorem schedule_realizes (orders : Nat → Schedule 8) (stage : Nat)
    (valid : Holds (MACNormalization.condition orders) (signature.needs (.schedule stage))) :
    (base orders).box (signature := signature) (MACNormalization.Atom.schedule stage) valid =
      ((MACNormalization.baseModel orders).atom (.schedule stage) valid).kernel := rfl

theorem eliminate_realizes (orders : Nat → Schedule 8) (stage : Nat)
    (valid : Holds (MACNormalization.condition orders) (signature.needs (.eliminate stage))) :
    (base orders).box (signature := signature) (MACNormalization.Atom.eliminate stage) valid =
      ((MACNormalization.baseModel orders).atom (.eliminate stage) valid).kernel := rfl

noncomputable def model (orders : Nat → Schedule 8) : CheckedModel relators (MACNormalization.condition orders) (family orders) where
  base := base orders
  localSound := by
    intro stage valid input
    simp only [relators, before, after, evaluate, base_schedule, base_eliminate, PMF.pure_bind]

def copy : Wiring signature finish (.pair finish finish) := .copy finish
def drop : Wiring signature finish .unit := .discard finish

def copiedRewrite (stage : Nat) :
    Step relators (.seq (before stage) (.wire copy)) (.seq (after stage) (.wire copy)) := .seqLeft (rewrite stage) _

def droppedRewrite (stage : Nat) :
    Step relators (.seq (before stage) (.wire drop)) (.seq (after stage) (.wire drop)) := .seqLeft (rewrite stage) _

theorem copied_support (stage : Nat) : (copiedRewrite stage).support = {stage, stage + 1} := by
  simp [copiedRewrite, rewrite, Step.support, Primitive.support, Relator.support, relators, before, after,
    Circuit.needs, signature, MACNormalization.layout]

theorem dropped_support (stage : Nat) : (droppedRewrite stage).support = {stage, stage + 1} := by
  simp [droppedRewrite, rewrite, Step.support, Primitive.support, Relator.support, relators, before, after,
    Circuit.needs, signature, MACNormalization.layout]

theorem copied_kernel (orders : Nat → Schedule 8) (stage : Nat)
    (valid : Holds (MACNormalization.condition orders) (Circuit.seq (before stage) (.wire copy)).needs) (input : Outcome) :
    evaluate (base orders) (.seq (before stage) (.wire copy)) valid input =
      PMF.pure (MACNormalization.sanitize input, MACNormalization.sanitize input) := by
  simp only [evaluate, before, base_schedule, base_eliminate, PMF.pure_bind, Foundation.Logic.Polygraph.StructuralTransport.Wire.eval, copy]

theorem dropped_kernel (orders : Nat → Schedule 8) (stage : Nat)
    (valid : Holds (MACNormalization.condition orders) (Circuit.seq (before stage) (.wire drop)).needs) (input : Outcome) :
    evaluate (base orders) (.seq (before stage) (.wire drop)) valid input = PMF.pure PUnit.unit := by
  simp only [evaluate, before, base_schedule, base_eliminate, PMF.pure_bind, Foundation.Logic.Polygraph.StructuralTransport.Wire.eval, drop]

theorem copied_retains_state_trace (input : Outcome) :
    (MACNormalization.sanitize input).state = input.state ∧
      (MACNormalization.sanitize input).trace = input.trace := ⟨rfl, rfl⟩

/-- The changed root stays guarded even if all its output is discarded. -/
theorem dropped_repair (old updated : Nat → Schedule 8) (stage : Nat) (changed : Finset Nat)
    (cached : Holds (MACNormalization.condition old) (droppedRewrite stage).support)
    (unchanged : ∀ label ∉ changed, old label = updated label)
    (rechecked : Holds (MACNormalization.condition updated) (fresh (droppedRewrite stage).support changed)) (input : Outcome) :
    let valid := repair cached (fun label outside proof => by
      simpa only [MACNormalization.condition, ← unchanged label outside] using proof) rechecked
    evaluate (base updated) (.seq (before stage) (.wire drop)) (valid.restrict (droppedRewrite stage).boundaries.1) input =
      evaluate (base updated) (.seq (after stage) (.wire drop)) (valid.restrict (droppedRewrite stage).boundaries.2) input := by
  apply (droppedRewrite stage).repaired (model updated) changed cached _ rechecked input
  intro label outside proof
  simpa only [MACNormalization.condition, ← unchanged label outside] using proof

def separatedChanges (stage : Nat) :
    Separated (relators := relators) (.tensorLeft (rewrite stage) (before (stage+1)))
      (.tensorRight (before stage) (rewrite (stage+1))) := .tensorLR _ _

theorem dropped_charge (stage : Nat) :
    ((Circuit.seq (before stage) (.wire drop)).charges).card = 1 := by
  simp [before, Circuit.charges, signature, MACNormalization.layout]

/-- An arbitrary prior context and the complete original input are retained.
Only the output of the original path is duplicated, without rerunning it. -/
theorem copied_joint {Context : Type} (orders : Nat → Schedule 8) (stage : Nat)
    (valid : Holds (MACNormalization.condition orders) (copiedRewrite stage).support)
    (law : PMF (Context × Outcome)) :
    law.bind (fun past => (evaluate (base orders) (.seq (before stage) (.wire copy))
      (valid.restrict (copiedRewrite stage).boundaries.1) past.2).map (fun next => (past, next))) =
    law.bind (fun past => (evaluate (base orders) (.seq (after stage) (.wire copy))
      (valid.restrict (copiedRewrite stage).boundaries.2) past.2).map (fun next => (past, next))) :=
  (copiedRewrite stage).sound_joint (model orders) valid _ _ law

/-- info: (false, false, true, true, true) -/
#guard_msgs in
#eval Id.run do
  let left := Step.tensorLeft (rewrite 0) (before 1)
  let right := Step.tensorRight (before 0) (rewrite 1)
  let copyPair : Circuit signature (.pair finish finish) (.pair (.pair finish finish) (.pair finish finish)) :=
    .wire (.copy (.pair finish finish))
  return ((rewrite 0).commute (rewrite 0) |>.isSome,
    (copiedRewrite 0).commute (copiedRewrite 0) |>.isSome,
    (left.commute right).isSome, (right.commute left).isSome,
    ((Step.seqLeft left copyPair).commute (Step.seqLeft right copyPair)).isSome)

/-- info: (2, 2, 1) -/
#guard_msgs in
#eval ((copiedRewrite 0).support.card, (droppedRewrite 0).support.card,
  (fresh (droppedRewrite 0).support {1}).card)

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC
