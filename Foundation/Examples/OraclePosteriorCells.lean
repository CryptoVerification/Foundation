import Foundation.Crypto.Logic.Polygraph.OraclePosteriorCells
import Foundation.Constructions.Symmetric.RandomFunctionMACProofEdits
import Foundation.Examples.ScheduleCertificate

/-! The mixed state-changing square on the same adaptive MAC, including its
last verification call. The distinct-coupling example in
RandomFunctionMACPosterior concerns the preceding three signing calls.
-/
namespace Foundation.Symmetric.RandomFunctionMACPosteriorCells
open Foundation.Probability CryptoOracle CryptoOracle.ProofEdits
open CryptoOracle.RandomOracle CryptoOracle.RandomOracle.Posterior
open CryptoOracle.ProofEdits.PosteriorCells RandomFunctionMACProofEdits
set_option backward.isDefEq.respectTransparency false

noncomputable def macSquare :=
  joint (localCachedRoutes RandomFunctionMACSchedules.Examples.attack) []

theorem before_eager :
    macSquare.map Corners.eagerBefore =
      (uniform (Fin 8 → Fin 256)).bind (fun function =>
        ((before RandomFunctionMACSchedules.Examples.attack).compile []).run functionOracle function) :=
  eager_before _ _

theorem before_lazy :
    macSquare.map Corners.lazyBefore =
      (before RandomFunctionMACSchedules.Examples.attack).run oracle [] [] := lazy_before _ _

theorem after_eager :
    macSquare.map Corners.eagerAfter =
      (uniform (Fin 8 → Fin 256)).bind (fun function =>
        ((cached RandomFunctionMACSchedules.Examples.attack).compile []).run functionOracle function) :=
  eager_after _ _

theorem after_lazy :
    macSquare.map Corners.lazyAfter =
      (cached RandomFunctionMACSchedules.Examples.attack).run oracle [] [] := lazy_after _ _

theorem same_function (square : Corners (Fin 8) (Fin 256) Bool)
    (supported : square ∈ macSquare.support) :
    square.eagerBefore.state = square.eagerAfter.state ∧
      square.eagerBefore.result = square.lazyBefore.result ∧
      square.eagerBefore.trace = square.lazyBefore.trace ∧
      ∀ input tag, square.lazyBefore.state.lookup input = some tag →
        square.eagerBefore.state input = tag := by
  obtain ⟨eager, _, result, trace, cache⟩ := compatible _ [] square supported
  exact ⟨congrArg Outcome.state eager, result, trace, cache⟩

end Foundation.Symmetric.RandomFunctionMACPosteriorCells
