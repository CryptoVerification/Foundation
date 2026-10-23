import Foundation.Crypto.Logic.Polygraph.MixedCircuitContextualHigher
import Foundation.Crypto.Logic.Polygraph.MixedCircuitPathExchange

/-! A supplied contextual higher presentation need only realize the actual
single separated-exchange generators. All whole-track exchanges are derived;
an arbitrary comparison of parallel paths is never an input generator. -/
namespace CryptoLogic.Polygraph.MixedCircuit.PresentedExchange
open Foundation.Logic.Polygraph
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}
set_option backward.isDefEq.respectTransparency false

structure Data (presentation : HigherBasis relators) where
  single : {a b : Port signature} → {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := relators) p q} →
    Exchange first second → PresentedCell (contextualBasis presentation) first second
  single_support : ∀ {a b : Port signature} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := relators) p q} (generator : Exchange first second),
    PresentedCell.support (single generator) = generator.support

variable {presentation : HigherBasis relators}

def Data.lift (data : Data presentation) {a b : Port signature} : {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := relators) p q} → Homotopy first second →
    PresentedCell (contextualBasis presentation) first second
  | _, _, _, _, .refl path => .refl path
  | _, _, _, _, .generator generator => data.single generator
  | _, _, _, _, .symm child => (data.lift child).symm
  | _, _, _, _, .trans first second => (data.lift first).trans (data.lift second)
  | _, _, _, _, .comp first second => .comp (data.lift first) (data.lift second)
  | _, _, _, _, .inverse child => .inverse (data.lift child)
  | _, _, _, _, .assoc p q r => .assoc p q r
  | _, _, _, _, .leftUnit path => .leftUnit path
  | _, _, _, _, .rightUnit path => .rightUnit path
  | _, _, _, _, .leftInv path => .leftInv path
  | _, _, _, _, .rightInv path => .rightInv path

theorem Data.lift_support (data : Data presentation) {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := relators) p q} (cell : Homotopy first second) :
    PresentedCell.support (data.lift cell) = Homotopy.support cell := by
  induction cell <;> simp_all only [Data.lift, PresentedCell.support, Homotopy.support, data.single_support]

end CryptoLogic.Polygraph.MixedCircuit.PresentedExchange
