import Foundation.Examples.OracleProofEditsBaseline
import Foundation.Crypto.Semantics.Oracle.PosteriorCoupling

/-! Ordinary invariant-proof baseline for the new, genuinely different
eager/lazy state types. Neither elementary edits nor their cells are imported.
It proves exactly the equality of chosen common realizations needed by the
mixed square. It may share all ordinary cache and sampling lemmas.
-/
namespace CryptoOracle.ProofEdits.Baseline
open Foundation.Probability Foundation.Symmetric.RandomFunctionMACProofEdits
open CryptoOracle.RandomOracle CryptoOracle.RandomOracle.Posterior
set_option backward.isDefEq.respectTransparency false
variable {Input Tag : Type} [DecidableEq Input] [DecidableEq Tag]
  [Fintype Input] [Fintype Tag] [Nonempty Tag]

theorem cached_completion_eq (attack : Program Input Tag (Input × Tag)) (signed : List Input) :
    completionJoint ((before attack).compile signed) =
      completionJoint ((cached attack).compile signed) := by
  have same := cached_eq attack oracle lazy_cache_laws signed []
  change ((before attack).compile signed).run oracle [] =
    ((cached attack).compile signed).run oracle [] at same
  simp only [completionJoint, retained]
  rw [same]

/-- The same state-changing marginal follows from an ordinary shared lemma.
It preserves the final signing history and ordered query/response transcript. -/
theorem cached_function_state (attack : Program Input Tag (Input × Tag)) (signed : List Input) :
    (completionJoint ((before attack).compile signed)).map Prod.fst =
      (uniform (Input → Tag)).bind (fun function =>
        ((cached attack).compile signed).run functionOracle function) := by
  rw [cached_completion_eq]
  exact completion_left _

end CryptoOracle.ProofEdits.Baseline
