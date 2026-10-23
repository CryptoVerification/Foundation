import Foundation.Logic.Polygraph.CartesianLaws
import Foundation.Crypto.Meta.Polygraph.Normalization

/-! Finite schematic four-dimensional coherence for all cryptographic
structural paths, retaining the exact code, loss and full witness values. -/
namespace CryptoLogic.Polygraph.CartesianCoherence
open Foundation.Logic.Polygraph
open General
universe u v a b p
set_option linter.checkUnivs false
variable {K : CodeSystem} {L : General.Language.{a, b} K}
  {P : Presented.Parameters.{a, b, p} L} {Γ : Presented.Context P}
  {S : General.Signature.{u, v} L} {X F}
  {d e : Derivation P Γ X F}

def compare (p q : Derivation.StructuralPath d e) : Cartesian.Cell4 p q :=
  Cartesian.coherent p q

theorem run_path (path : Derivation.StructuralPath d e) (code : K.Code (L.machine X)) :
    Derivation.run d code = Derivation.run e code := Derivation.run_path path code

theorem loss_path (path : Derivation.StructuralPath d e) (M : Presented.Interpretation P S) :
    Derivation.loss M d = Derivation.loss M e := Derivation.loss_path path M

theorem witnesses_path (path : Derivation.StructuralPath d e) (M : Presented.Interpretation P S)
    (A) (W : (S.interpret X).Witness (M.family F) A) :
    Derivation.runWitnesses M d A W = Derivation.runWitnesses M e A W :=
  Derivation.witnesses_path path M A W

end CryptoLogic.Polygraph.CartesianCoherence
