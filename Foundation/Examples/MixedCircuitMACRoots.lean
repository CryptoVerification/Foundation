import Foundation.Examples.MixedCircuitMAC
import Foundation.Crypto.Logic.Polygraph.MixedCircuitRootResolution
import Mathlib.Order.WellFounded

/-! Root overlap and termination evidence for the existing MAC catalogue,
under arbitrary mixed sequence/tensor contexts. Pure wiring remains fixed;
this is not yet a combined structural-and-cryptographic critical-pair basis. -/
namespace CryptoLogic.Polygraph.MixedCircuit
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
namespace Examples.MAC
set_option backward.isDefEq.respectTransparency false

def boxCount : {n m : Port signature} → Circuit signature n m → Nat
  | _, _, .wire _ => 0
  | _, _, .box _ => 1
  | _, _, .seq left right => boxCount left + boxCount right
  | _, _, .tensor left right => boxCount left + boxCount right

/-- Every actual rewrite removes exactly one box, including under copy/drop
contexts. A pure wire itself is not rewritten in this catalogue. -/
theorem step_count {n m} {a b : Circuit signature n m} (change : Step relators a b) :
    boxCount b + 1 = boxCount a := by
  induction change with
  | root primitive =>
      cases primitive with
      | rule stage => rfl
  | seqLeft child fixed ih | tensorLeft child fixed ih => simp only [boxCount]; omega
  | seqRight fixed child ih | tensorRight fixed child ih => simp only [boxCount]; omega

theorem terminating (n m : Port signature) :
    WellFounded (fun b a : Circuit signature n m => Nonempty (Step relators a b)) :=
  Subrelation.wf
    (fun {b a} ⟨change⟩ => by
      change boxCount b < boxCount a
      have equality := step_count change
      omega)
    (measure (fun circuit : Circuit signature n m => boxCount circuit)).wf

theorem no_box_step (label : MACNormalization.Atom) {b : Circuit signature (signature.inputs label) (signature.outputs label)}
    (change : Step relators (.box label) b) : False := by
  cases label <;> cases change with
  | root primitive => cases primitive

theorem no_wire_step {n m} (wire : Wiring signature n m) {b : Circuit signature n m}
    (change : Step relators (.wire wire) b) : False := by
  cases change with
  | root primitive => cases primitive

/-- Any change whose source is this local redex must be the same indexed
root. There is no proper inner redex in either of its two box leaves. -/
theorem root_unique (stage : Nat) {b : Circuit signature (source (stage + 1)) finish}
    (change : Step relators (before stage) b) :
    b = after stage ∧ HEq change (rewrite stage) := by
  cases change with
  | root primitive =>
      cases primitive with
      | rule other => exact ⟨rfl, HEq.rfl⟩
  | seqLeft inner fixed => exact False.elim (no_box_step _ inner)
  | seqRight fixed inner => exact False.elim (no_box_step _ inner)

theorem roots_rigid : RootRigid relators := by
  intro n m a b primitive c other
  cases primitive with
  | rule stage => exact root_unique stage other

def resolve {n m} {a b c : Circuit signature n m} (first : Step relators a b) (second : Step relators a c) :
    Resolution first second := first.resolve roots_rigid second

def localJoin {n m} {a b c : Circuit signature n m} (first : Step relators a b) (second : Step relators a c) :
    LocalJoin first second := first.localJoin roots_rigid second

end Examples.MAC
end CryptoLogic.Polygraph.MixedCircuit
