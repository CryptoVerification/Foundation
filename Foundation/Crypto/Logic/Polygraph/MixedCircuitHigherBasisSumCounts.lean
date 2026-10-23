import Foundation.Crypto.Logic.Polygraph.MixedCircuitHigherBasisSum

/-! The sum embeddings retain every Four syntax node. This counts higher
constructors only, excluding boundary/context/generator payloads and bytes. -/
namespace CryptoLogic.Polygraph.MixedCircuit.PresentedCell
open Foundation.Logic.Polygraph
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}
variable {left right : HigherBasis relators}

theorem injectLeft_constructorCount (right : HigherBasis relators) {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := relators) p q} (cell : PresentedCell left first second) :
    constructorCount (cell.injectLeft right) = constructorCount cell := by
  induction cell <;> simp_all only [injectLeft, constructorCount]

theorem injectRight_constructorCount (left : HigherBasis relators) {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := relators) p q} (cell : PresentedCell right first second) :
    constructorCount (cell.injectRight left) = constructorCount cell := by
  induction cell <;> simp_all only [injectRight, constructorCount]

end CryptoLogic.Polygraph.MixedCircuit.PresentedCell
