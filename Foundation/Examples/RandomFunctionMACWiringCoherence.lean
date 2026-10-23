import Foundation.Logic.Polygraph.FiniteWiringCoherence
import Foundation.Examples.RandomFunctionMACFiniteWiring

/-! Compare actual generated wiring proof data, not just equal endpoints.
One example compares a proof with a redundant unit loop. Another compares
left-first and right-first transformations of two independent wiring blocks,
then lifts both orders to the same single live-cache MAC execution. -/
namespace Foundation.Symmetric.RandomFunctionMACWiringCoherence
open Foundation.Logic.Polygraph
open StructuralTransport
open CryptoOracle CryptoOracle.RandomOracle
open RandomFunctionMACFiniteWiring (compiledView compiledCopy certificate inverseCertificate inverseCircuit identityCircuit)
open RandomFunctionMACStructuralTransport (recordShape view)
open RandomFunctionMACSharedReferences (codecs route)
open RandomFunctionMACRepresentationSwitch (oldCodec old_oracle choose)
open RandomFunctionMACNativeCaller (target)

def cancelledLoop : FiniteWiring.Cell compiledView compiledView :=
  .trans (.symm (.seqRightUnit compiledView)) (.seqRightUnit compiledView)

def withLoop : FiniteWiring.Cell compiledView compiledCopy := .trans cancelledLoop certificate

def comparison : FiniteWiring.Higher.Four certificate withLoop := FiniteWiring.Higher.coherent certificate withLoop

theorem different_costs : certificate.steps ≠ withLoop.steps := by
  have growth (count : Nat) : count ≠ 2 + count := by omega
  exact growth certificate.steps

theorem steps_not_invariant :
    ¬ ∀ {n m : Nat} {first second : FiniteWiring.Circuit n m}
      {one two : FiniteWiring.Cell first second}, FiniteWiring.Higher.Four one two → one.steps = two.steps := by
  intro invariant
  exact different_costs (invariant comparison)

def leftThenRight := FiniteWiring.Cell.trans
  (.tensor certificate (.refl (Finite.compile inverseCircuit)))
  (.tensor (.refl compiledCopy) inverseCertificate)

def rightThenLeft := FiniteWiring.Cell.trans
  (.tensor (.refl compiledView) inverseCertificate)
  (.tensor certificate (.refl (Finite.compile identityCircuit)))

def independentOrders : FiniteWiring.Higher.Four leftThenRight rightThenLeft :=
  FiniteWiring.Higher.tensorInterchange certificate inverseCertificate

def combinedBefore := Wire.tensor view inverseCircuit
def combinedAfter := Wire.tensor (Wire.copy recordShape) identityCircuit

abbrev Past := Representation.Switch.Past (Fin 8) (Fin 256) Bool (Fin 256)

def inputs (_ : Past) : (Shape.pair recordShape (.pair (.pair recordShape recordShape) recordShape)).Value
    (fun _ => SharedReference.Ref) := (.root, ((.root, .root), .root))

def combinedRoute (past : Past) (refs :
    (Shape.pair (.pair recordShape recordShape) (.pair (.pair recordShape recordShape) recordShape)).Value
      (fun _ => SharedReference.Ref)) : Nat → SharedReference.Ref := route past refs.1

noncomputable def beforeGame := Representation.SharedSwitch.wired oldCodec codecs choose combinedBefore inputs combinedRoute 1 target []
noncomputable def afterGame := Representation.SharedSwitch.wired oldCodec codecs choose combinedAfter inputs combinedRoute 1 target []

theorem live_left_then_right : beforeGame = afterGame :=
  Representation.SharedSwitch.compiled_cell_joint (one := combinedBefore) (two := combinedAfter) leftThenRight oldCodec codecs choose inputs combinedRoute 1 target []

theorem live_right_then_left : beforeGame = afterGame :=
  Representation.SharedSwitch.compiled_cell_joint (one := combinedBefore) (two := combinedAfter) rightThenLeft oldCodec codecs choose inputs combinedRoute 1 target []

theorem decoded_full_game :
    afterGame.map (fun pair => (Representation.Switch.decode oldCodec codecs pair.2).2.2) =
      target.run RandomOracle.oracle [] := by
  have law := Representation.SharedSwitch.final_game oldCodec codecs choose
    (fun past => combinedAfter.eval (fun _ => SharedReference.Ref) (inputs past)) combinedRoute 1 target []
  change afterGame.map (fun pair => (Representation.Switch.decode oldCodec codecs pair.2).2.2) =
    target.run (Representation.oracle oldCodec) [] at law
  rw [old_oracle] at law
  exact law

/-- info: (43, 45, 204, 279, 63, 63, 0, 6) -/
#guard_msgs in
#eval (certificate.steps, withLoop.steps, comparison.generatorCount, comparison.lawCount,
  leftThenRight.steps, rightThenLeft.steps, independentOrders.generatorCount, independentOrders.lawCount)

end Foundation.Symmetric.RandomFunctionMACWiringCoherence
