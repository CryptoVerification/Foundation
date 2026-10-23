import Foundation.Crypto.Semantics.Oracle.FiniteWiringSwitch
import Foundation.Logic.Polygraph.StructuralWiringBoundary
import Foundation.Examples.RandomFunctionMACSharedReferences

/-! Automatically synthesized primitive wiring certificates for the actual
live-cache alias circuit. The inverse-associator case demonstrates a missing
law in the previous nine-root source language, not a new mathematical law.
Rejection is complete for all atomic interpretations, not just Ref.root. -/
namespace Foundation.Symmetric.RandomFunctionMACFiniteWiring
open Foundation.Logic.Polygraph
open StructuralTransport
open CryptoOracle CryptoOracle.RandomOracle
open RandomFunctionMACStructuralTransport (recordShape view)
open RandomFunctionMACRepresentationSwitch (oldCodec choose)
open RandomFunctionMACSharedReferences (codecs inputs route game simpleGame)
open RandomFunctionMACNativeCaller (target)

def compiledView := Finite.compile view
def compiledCopy := Finite.compile (Wire.copy recordShape)

theorem accepts_view : (FiniteWiring.synthesize compiledView compiledCopy).isSome = true := by decide_cbv

def certificate : FiniteWiring.Cell compiledView compiledCopy :=
  (FiniteWiring.synthesize compiledView compiledCopy).get accepts_view

theorem generated_live_game : game = simpleGame :=
  Representation.SharedSwitch.compiled_cell_joint certificate oldCodec codecs choose inputs route 1 target []

def inverseCircuit := Wire.seq (Wire.assoc recordShape recordShape recordShape)
  (Wire.unassoc recordShape recordShape recordShape)
def identityCircuit := Wire.identity (Shape.pair (.pair recordShape recordShape) recordShape)

theorem accepts_inverse :
    (FiniteWiring.synthesize (Finite.compile inverseCircuit) (Finite.compile identityCircuit)).isSome = true := by decide_cbv

def inverseCertificate : FiniteWiring.Cell (Finite.compile inverseCircuit) (Finite.compile identityCircuit) :=
  (FiniteWiring.synthesize (Finite.compile inverseCircuit) (Finite.compile identityCircuit)).get accepts_inverse

theorem previous_basis_missing : ¬ Nonempty (StructuralTransport.Cell inverseCircuit identityCircuit) :=
  Boundary.old_inverse_missing recordShape recordShape recordShape

def swapped := Wire.swap recordShape recordShape
def unchanged := Wire.identity (Shape.pair recordShape recordShape)

theorem rejects_different_routing :
    (FiniteWiring.synthesize (Finite.compile swapped) (Finite.compile unchanged)).isSome = false := by decide_cbv

theorem singleton_reference_model_same (value : Shape.Value (fun _ => SharedReference.Ref) (.pair recordShape recordShape)) :
    swapped.eval (fun _ => SharedReference.Ref) value = unchanged.eval (fun _ => SharedReference.Ref) value := by
  rcases value with ⟨one, two⟩
  cases one
  cases two
  rfl

/-- info: (true, true, false, 43, 20) -/
#guard_msgs in
#eval ((FiniteWiring.synthesize compiledView compiledCopy).isSome,
  (FiniteWiring.synthesize (Finite.compile inverseCircuit) (Finite.compile identityCircuit)).isSome,
  (FiniteWiring.synthesize (Finite.compile swapped) (Finite.compile unchanged)).isSome,
  certificate.steps, inverseCertificate.steps)

end Foundation.Symmetric.RandomFunctionMACFiniteWiring
