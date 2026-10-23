import Foundation.Crypto.Logic.Polygraph.MixedCircuitContextualHigher

/-! Combine two explicitly supplied higher presentations of the same actual
rewrite language. Every old derivation and its full support is retained. No
completeness or finiteness of either input is inferred. -/
namespace CryptoLogic.Polygraph.MixedCircuit
open Foundation.Logic.Polygraph
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}
set_option backward.isDefEq.respectTransparency false

def HigherBasis.sum (left right : HigherBasis relators) : HigherBasis relators where
  Generator := fun first second => Sum (left.Generator first second) (right.Generator first second)
  requirements := fun generator => match generator with
    | .inl generator => left.requirements generator
    | .inr generator => right.requirements generator
  covered := by
    intro a b p q first second generator
    cases generator with
    | inl generator => exact left.covered generator
    | inr generator => exact right.covered generator

namespace PresentedCell
variable {left right : HigherBasis relators}

def injectLeft (right : HigherBasis relators) {a b : Port signature} : {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := relators) p q} → PresentedCell left first second →
    PresentedCell (left.sum right) first second
  | _, _, _, _, .refl path => .refl path
  | _, _, _, _, .generator generator => .generator (.inl generator)
  | _, _, _, _, .symm child => (injectLeft right child).symm
  | _, _, _, _, .trans first second => (injectLeft right first).trans (injectLeft right second)
  | _, _, _, _, .comp first second => .comp (injectLeft right first) (injectLeft right second)
  | _, _, _, _, .inverse child => .inverse (injectLeft right child)
  | _, _, _, _, .assoc p q r => .assoc p q r
  | _, _, _, _, .leftUnit path => .leftUnit path
  | _, _, _, _, .rightUnit path => .rightUnit path
  | _, _, _, _, .leftInv path => .leftInv path
  | _, _, _, _, .rightInv path => .rightInv path

def injectRight (left : HigherBasis relators) {a b : Port signature} : {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := relators) p q} → PresentedCell right first second →
    PresentedCell (left.sum right) first second
  | _, _, _, _, .refl path => .refl path
  | _, _, _, _, .generator generator => .generator (.inr generator)
  | _, _, _, _, .symm child => (injectRight left child).symm
  | _, _, _, _, .trans first second => (injectRight left first).trans (injectRight left second)
  | _, _, _, _, .comp first second => .comp (injectRight left first) (injectRight left second)
  | _, _, _, _, .inverse child => .inverse (injectRight left child)
  | _, _, _, _, .assoc p q r => .assoc p q r
  | _, _, _, _, .leftUnit path => .leftUnit path
  | _, _, _, _, .rightUnit path => .rightUnit path
  | _, _, _, _, .leftInv path => .leftInv path
  | _, _, _, _, .rightInv path => .rightInv path

theorem injectLeft_support (right : HigherBasis relators) {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := relators) p q} (cell : PresentedCell left first second) :
    PresentedCell.support (cell.injectLeft right) = PresentedCell.support cell := by
  induction cell <;> simp_all only [injectLeft, PresentedCell.support, HigherBasis.sum]

theorem injectRight_support (left : HigherBasis relators) {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := relators) p q} (cell : PresentedCell right first second) :
    PresentedCell.support (cell.injectRight left) = PresentedCell.support cell := by
  induction cell <;> simp_all only [injectRight, PresentedCell.support, HigherBasis.sum]

end PresentedCell
end CryptoLogic.Polygraph.MixedCircuit
