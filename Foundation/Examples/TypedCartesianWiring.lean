import Foundation.Crypto.Logic.Polygraph.MixedCartesianWiring
import Foundation.Examples.MixedCircuitMAC

/-! Many-sorted first-level wiring certificates, a negative routing check,
and actual full-state MAC contexts. No higher coherence or runtime comparison
is claimed by these diagnostics. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Examples

def a : Shape (Fin 2) := .atom 0
def b : Shape (Fin 2) := .atom 1

def doubleSwap : Wire (.pair a b) (.pair a b) := .seq (.swap a b) (.swap b a)
def unitCancellation : Wire a a := .seq (.leftUnitInv a) (.leftUnit a)
def duplicateDiscard : Wire a a := .seq (.seq (.copy a) (.tensor (.discard a) (.identity a))) (.leftUnit a)

def swapCertificate : Cell doubleSwap (.identity (.pair a b)) :=
  connect _ _ ((TypedRouting.normal_complete _ _).mpr (fun _ _ => rfl))

def inverseCertificate : Cell unitCancellation (.identity a) := leftUnit_inverse a

theorem swap_rejected : equivalent (.swap a a) (.identity (.pair a a)) = false := by decide_cbv

/-- info: (true, true, true, false, true, true) -/
#guard_msgs in
#eval (equivalent doubleSwap (.identity (.pair a b)), equivalent unitCancellation (.identity a),
  equivalent duplicateDiscard (.identity a), equivalent (.swap a a) (.identity (.pair a a)),
  (certify doubleSwap (.identity (.pair a b))).isSome, (certify unitCancellation (.identity a)).isSome)

def sampleFamily (name : Fin 2) : Type := if name = 0 then Bool else Nat

/-- info: (true, 37) -/
#guard_msgs in
#eval (show Bool × Nat from doubleSwap.eval sampleFamily (show Bool × Nat from (true, 37)))

/-- info: (true, true, true) -/
#guard_msgs in
#eval (equivalent (Wire.seq (.assoc a b a) (.unassoc a b a)) (.identity (.pair (.pair a b) a)),
  equivalent (Wire.seq (.rightUnitInv b) (.rightUnit b)) (.identity b),
  equivalent (Wire.identity (.unit : Shape (Fin 2))) (.discard .unit))

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Examples

namespace CryptoLogic.Polygraph.MixedCircuit.Examples.TypedCartesian
open Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.StructuralTransport
open Foundation.Probability
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples
open Foundation.Logic.Polygraph.ScheduleCertificate
set_option backward.isDefEq.respectTransparency false

def unitCancellation : Wiring MAC.signature MAC.finish MAC.finish := .seq (.leftUnitInv MAC.finish) (.leftUnit MAC.finish)

noncomputable def model (orders : Nat → Schedule 8) :
    CheckedModel (CartesianWiring.relators (signature := MAC.signature)) (MACNormalization.condition orders) (MAC.family orders) :=
  CartesianWiring.checkedModel (MAC.base orders)

def copiedNormalization (stage : Nat) :=
  (Placement.seqLeft (.wire (.copy (.pair MAC.finish MAC.finish)))).track
    ((Placement.tensorRight (MAC.before stage)).track (CartesianWiring.normalization unitCancellation))

def discardedNormalization (stage : Nat) :=
  (Placement.seqLeft (.wire (.discard (.pair MAC.finish MAC.finish)))).track
    ((Placement.tensorRight (MAC.before stage)).track (CartesianWiring.normalization unitCancellation))

theorem copiedNormalization_support (stage : Nat) : RewriteTrack.support (copiedNormalization stage) = {stage} := by
  simp [copiedNormalization, Placement.track_support, CartesianWiring.normalization_support,
    Placement.needs, MAC.before, Circuit.needs, MAC.signature, MACNormalization.layout]

theorem discardedNormalization_support (stage : Nat) : RewriteTrack.support (discardedNormalization stage) = {stage} := by
  simp [discardedNormalization, Placement.track_support, CartesianWiring.normalization_support,
    Placement.needs, MAC.before, Circuit.needs, MAC.signature, MACNormalization.layout]

theorem mac_repaired_joint {Context : Type} (old updated : Nat → Schedule 8) (stage : Nat) (changed : Finset Nat)
    (cached : Holds (MACNormalization.condition old) {stage})
    (unchanged : ∀ label ∉ changed, old label = updated label)
    (rechecked : Holds (MACNormalization.condition updated) (fresh {stage} changed))
    (law : PMF (Context × Bundle (MAC.family updated) (MAC.source (stage + 1)))) :
    ∃ left : Holds (MACNormalization.condition updated) (Circuit.seq (MAC.before stage) (.wire unitCancellation)).needs,
    ∃ right : Holds (MACNormalization.condition updated)
      (Circuit.seq (MAC.before stage) (.wire (Cartesian.reify (TypedRouting.normal unitCancellation)))).needs,
      law.bind (fun past => (evaluate (MAC.base updated) (.seq (MAC.before stage) (.wire unitCancellation)) left past.2).map (fun next => (past, next))) =
      law.bind (fun past => (evaluate (MAC.base updated) (.seq (MAC.before stage)
        (.wire (Cartesian.reify (TypedRouting.normal unitCancellation)))) right past.2).map (fun next => (past, next))) := by
  let place : Placement (signature := MAC.signature) MAC.finish MAC.finish (MAC.source (stage + 1)) MAC.finish :=
    Placement.seqRight (MAC.before stage)
  have guards : place.needs = {stage} := by
    simp [place, Placement.needs, MAC.before, Circuit.needs, MAC.signature, MACNormalization.layout]
  have cached' : Holds (MACNormalization.condition old) place.needs := by rw [guards]; exact cached
  have rechecked' : Holds (MACNormalization.condition updated) (fresh place.needs changed) := by rw [guards]; exact rechecked
  exact CartesianWiring.normalized_repaired_joint (MAC.base updated) unitCancellation place changed cached'
    (fun label outside proof => by simpa only [MACNormalization.condition, ← unchanged label outside] using proof)
    rechecked' law

/-- info: (1, 1) -/
#guard_msgs in
#eval ((RewriteTrack.support (copiedNormalization 0)).card,
  (RewriteTrack.support (discardedNormalization 0)).card)

end CryptoLogic.Polygraph.MixedCircuit.Examples.TypedCartesian
