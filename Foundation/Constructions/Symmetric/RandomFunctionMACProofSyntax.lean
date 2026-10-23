import Foundation.Crypto.Logic.Polygraph.OracleProofEdits
import Foundation.Constructions.Symmetric.RandomFunctionMACSchedules

/-! Shared game and reduction syntax for comparing elementary diagram proofs
with ordinary invariant proofs. This module has no dependency on LocalEdit or
the stochastic interpretation of cells. -/
namespace Foundation.Symmetric.RandomFunctionMACProofEdits
open CryptoOracle CryptoOracle.ProofEdits
variable {Input Tag : Type} [DecidableEq Input] [DecidableEq Tag]

/-- Record signing before lookup, and test final freshness before verification. -/
def before : Program Input Tag (Input × Tag) → Command Input Tag Bool
  | .done (message, guess) => .fresh message (fun fresh => .query message
      (fun tag => .done (fresh && decide (tag = guess))))
  | .query message next => .record message (.query message (fun tag => before (next tag)))
  | .coin next => .coin (fun bit => before (next bit))

/-- Record signing after lookup, and test final freshness after verification. -/
def after : Program Input Tag (Input × Tag) → Command Input Tag Bool
  | .done (message, guess) => .query message (fun tag => .fresh message
      (fun fresh => .done (fresh && decide (tag = guess))))
  | .query message next => .query message (fun tag => .record message (after (next tag)))
  | .coin next => .coin (fun bit => after (next bit))

/-- Recall the first observed response throughout the remaining adaptive game. -/
def cached (attack : Program Input Tag (Input × Tag)) : Command Input Tag Bool :=
  (after attack).remember

/-- The unedited reduction returns the verdict and hides its private history. -/
def distinguisher (attack : Program Input Tag (Input × Tag)) : Program Input Tag Bool :=
  ((before attack).compile []).bind (fun result => .done result.1)

/-- The cache-dependent edited reduction is actual oracle program syntax. -/
def cachedDistinguisher (attack : Program Input Tag (Input × Tag)) : Program Input Tag Bool :=
  (cached attack).finish []

end Foundation.Symmetric.RandomFunctionMACProofEdits
