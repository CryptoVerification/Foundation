import Foundation.Examples.GameProofMACNativeQuantitative
import Foundation.Examples.MixedCircuitMAC

/-! Native quantitative interpretation of the actual MAC boxes and their
serial circuit fragment. The concrete preparation/elimination root compares
two certified reductions. Tensor/copy/discard computational interpretations
are not inferred from this serial interpretation. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.NativeReduction
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open Foundation.Logic.Polygraph.ScheduleCertificate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

inductive Serial : {a b : MACNormalization.Vertex} → Circuit signature (.atom a) (.atom b) → Type where
  | identity (a : MACNormalization.Vertex) : Serial (.wire (.identity (.atom a)))
  | box (label : MACNormalization.Atom) : Serial (.box (signature := signature) label)
  | seq {a b c : MACNormalization.Vertex} {first : Circuit signature (.atom a) (.atom b)}
      {second : Circuit signature (.atom b) (.atom c)} :
      Serial first → Serial second → Serial (.seq first second)

def Serial.plan : {a b : MACNormalization.Vertex} → {circuit : Circuit signature (.atom a) (.atom b)} →
    Serial circuit → Plan MACNormalization.layout a b
  | _, _, _, .identity a => .identity a
  | _, _, _, .box label => .atom label
  | _, _, _, .seq first second => .seq first.plan second.plan

theorem Serial.needs {a b : MACNormalization.Vertex} {circuit : Circuit signature (.atom a) (.atom b)}
    (serial : Serial circuit) : serial.plan.needs MACNormalization.layout = circuit.needs := by
  induction serial with
  | identity => rfl
  | box => rfl
  | seq first second one two => simp only [Serial.plan, Plan.needs, Circuit.needs, one, two]

noncomputable def Serial.extract (orders : Nat → Schedule 8) {a b : MACNormalization.Vertex}
    {circuit : Circuit signature (.atom a) (.atom b)} (serial : Serial circuit)
    (valid : Holds (MACNormalization.condition orders) circuit.needs) :
    General.QuantitativeReduction (MACNativeQuantitative.object orders a) (MACNativeQuantitative.object orders b) :=
  Quantitative.evaluate (MACNativeQuantitative.base orders) serial.plan (by rw [serial.needs]; exact valid)

def beforeSerial (stage : Nat) : Serial (before stage) := .seq (.box (.schedule stage)) (.box (.eliminate stage))
def afterSerial (stage : Nat) : Serial (after stage) := .box (.eliminate (stage + 1))

theorem root_comparison (orders : Nat → Schedule 8) (stage : Nat)
    (left : Holds (MACNormalization.condition orders) (before stage).needs)
    (right : Holds (MACNormalization.condition orders) (after stage).needs) :
    General.QuantitativeComparison ((beforeSerial stage).extract orders left) ((afterSerial stage).extract orders right) := by
  exact (MACNativeQuantitative.model orders).comparison stage _ _ (fun _ member => False.elim (Finset.notMem_empty _ member))

theorem serial_code (orders : Nat → Schedule 8) {a b : MACNormalization.Vertex}
    {circuit : Circuit signature (.atom a) (.atom b)}
    (serial : Serial circuit) (valid : Holds (MACNormalization.condition orders) circuit.needs)
    (code : CryptoOracle.Interactive.Code) : (serial.extract orders valid).compiler.run code = code := by
  induction serial generalizing code with
  | identity => rfl
  | box label => cases label <;> rfl
  | seq first second one two =>
      exact (two (valid.restrict Finset.subset_union_right) _).trans
        (one (valid.restrict Finset.subset_union_left) code)

theorem root_repaired (old updated : Nat → Schedule 8) (stage : Nat) (changed : Finset Nat)
    (cached : Holds (MACNormalization.condition old) (rewrite stage).support)
    (unchanged : ∀ label ∉ changed, old label = updated label)
    (rechecked : Holds (MACNormalization.condition updated) (fresh (rewrite stage).support changed)) :
    let valid := repair cached (fun label outside proof => by
      simpa only [MACNormalization.condition, ← unchanged label outside] using proof) rechecked
    General.QuantitativeComparison
      ((beforeSerial stage).extract updated (valid.restrict (rewrite stage).boundaries.1))
      ((afterSerial stage).extract updated (valid.restrict (rewrite stage).boundaries.2)) := by
  exact root_comparison updated stage _ _

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.NativeReduction
