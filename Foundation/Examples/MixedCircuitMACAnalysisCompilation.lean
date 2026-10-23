import Foundation.Crypto.Logic.Polygraph.MixedCircuitRepresentation
import Foundation.Examples.MixedCircuitMAC

/-! Compile one-input MAC analysis to a finite mask of output verdicts.
Secret state and transcript are retained by a logical representation; native
code will generate the verdict bits only. This is not serialization of an
oracle's hidden state, nor a compiler for arbitrary probabilistic boxes. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.AnalysisCompilation
open Foundation.Probability
open Foundation.Logic.Polygraph.StructuralTransport
open Foundation.Logic.Polygraph.ScheduleCertificate
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
set_option backward.isDefEq.respectTransparency false

abbrev Bits (_ : signature.PortAtom) := Bool

def output : {n m : Port signature} → Circuit signature n m → Bundle Bits n → Bundle Bits m
  | _, _, .wire wire, input => wire.eval Bits input
  | _, _, .box (.schedule _), input => input
  | _, _, .box (.eliminate _), _ => false
  | _, _, .seq first second, input => output second (output first input)
  | _, _, .tensor first second, input => (output first input.1, output second input.2)

noncomputable def model (orders : Nat → Schedule 8) : Model signature (MACNormalization.condition orders) Bits where
  box label _ input := PMF.pure (match label with | .schedule _ => input | .eliminate _ => false)

theorem evaluate_bits (orders : Nat → Schedule 8) {n m} (circuit : Circuit signature n m)
    (valid : Holds (MACNormalization.condition orders) circuit.needs) (input : Bundle Bits n) :
    MixedCircuit.evaluate (model orders) circuit valid input = PMF.pure (output circuit input) := by
  induction circuit with
  | wire => rfl
  | box label => cases label <;> rfl
  | seq first second one two => simp only [MixedCircuit.evaluate, output, one, PMF.pure_bind, two]
  | tensor first second one two => simp only [MixedCircuit.evaluate, output, one, PMF.pure_bind, two, PMF.pure_map, append]

def restore (orders : Nat → Schedule 8) (seed : Outcome) (vertex : signature.PortAtom) (keep : Bool) : family orders vertex :=
  match vertex with
  | .stage _ => if keep then seed else MACNormalization.sanitize seed
  | .finish => if keep then seed else MACNormalization.sanitize seed

-- The original full payload is shared as proof data, never read by native instructions.
theorem restore_false (orders : Nat → Schedule 8) (seed : Outcome) (vertex : signature.PortAtom) :
    restore orders seed vertex false = restore orders (MACNormalization.sanitize seed) vertex true := by
  cases vertex <;> rfl

theorem representation (orders : Nat → Schedule 8) (seed : Outcome) :
    Representation (model orders) (MAC.base orders) (restore orders seed) := by
  constructor
  intro label valid input
  cases label with
  | schedule stage =>
      simp only [model, PMF.pure_map, base_schedule]
      rfl
  | eliminate stage =>
      simp only [model, PMF.pure_map, base_eliminate]
      cases input <;> rfl

def mask {stage : Nat} {m} (circuit : Circuit signature (source stage) m) : Bundle Bits m := output circuit true

def flatten : (shape : Port signature) → Bundle Bits shape → List Bool
  | .atom _, bit => [bit]
  | .unit, _ => []
  | .pair left right, pair => flatten left pair.1 ++ flatten right pair.2

def width : Port signature → Nat
  | .atom _ => 1
  | .unit => 0
  | .pair left right => width left + width right

theorem flatten_length (shape : Port signature) (bits : Bundle Bits shape) : (flatten shape bits).length = width shape := by
  induction shape with
  | atom => rfl
  | unit => rfl
  | pair left right one two => simp only [flatten, width, List.length_append, one, two]

def flags {stage : Nat} {m} (circuit : Circuit signature (source stage) m) : List Bool := flatten m (mask circuit)

theorem flags_length {stage : Nat} {m} (circuit : Circuit signature (source stage) m) :
    (flags circuit).length = width m := flatten_length m _

/-- All full outcomes, including their state and complete transcript, are
reconstructed from the native verdict mask and the same sampled seed. -/
theorem compile_correct (orders : Nat → Schedule 8) {stage : Nat} {m}
    (circuit : Circuit signature (source stage) m)
    (valid : Holds (MACNormalization.condition orders) circuit.needs) (seed : Outcome) :
    MixedCircuit.evaluate (MAC.base orders) circuit valid seed =
      PMF.pure (m.map (restore orders seed) (mask circuit)) := by
  have same := (representation orders seed).evaluate circuit valid true
  rw [evaluate_bits] at same
  simpa only [PMF.pure_map, source, Shape.map, restore, mask, if_true] using same.symm

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.AnalysisCompilation
