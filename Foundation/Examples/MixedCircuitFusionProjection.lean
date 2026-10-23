import Foundation.Examples.MixedCircuitFusionHigher

/-! Project every new higher cell back to the old presentation while retaining
its exact declared guard footprint. This proves relative conservativity, not
global coherence or finite completeness of either presentation. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural.Fusion
open Foundation.Logic.Polygraph
set_option backward.isDefEq.respectTransparency false

structure OldExactCell {a b} {p q : Circuit signature a b}
    (first second : RewriteTrack (relators := @Structural.rules true) p q) (footprint : Finset Nat) where
  cell : MixedCell first second
  support_eq : PresentedCell.support cell = footprint

def projectRoot {a b} {p q : Circuit signature a b} {first second : RewriteTrack (relators := rules) p q}
    (generator : Generator first second) :
    OldExactCell (expandTrack first) (expandTrack second) (baseBasis.requirements generator) := by
  cases generator with
  | existing old =>
      simp only [expand_embedTrack]
      exact ⟨.generator old, rfl⟩
  | definition p q tail =>
      simp only [expand_embedTrack]
      refine ⟨.refl _, ?_⟩
      simp only [PresentedCell.support, baseBasis, expandTrack, expandStep_support, suffixStep_support]

def projectGenerator : {a b : Port signature} → {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := rules) p q} → (generator : ContextualGenerator baseBasis first second) →
    OldExactCell (expandTrack first) (expandTrack second) generator.support
  | _, _, _, _, _, _, .root generator => projectRoot generator
  | _, _, _, _, _, _, .placed place child => by
      simp only [expandTrack_placement]
      let projected := projectGenerator child
      refine ⟨projected.cell.whisker place, ?_⟩
      simp only [PresentedCell.whisker_support, projected.support_eq, ContextualGenerator.support]

def projectCell {a b : Port signature} : {p q : Circuit signature a b} →
    {first second : RewriteTrack (relators := rules) p q} → (cell : Cell first second) →
    OldExactCell (expandTrack first) (expandTrack second) (PresentedCell.support cell)
  | _, _, _, _, .refl path => ⟨.refl _, expandTrack_support path⟩
  | _, _, _, _, .generator generator => projectGenerator generator
  | _, _, _, _, .symm child =>
      let one := projectCell child
      ⟨one.cell.symm, one.support_eq⟩
  | _, _, _, _, .trans first second =>
      let one := projectCell first
      let two := projectCell second
      ⟨one.cell.trans two.cell, by simp only [PresentedCell.support, one.support_eq, two.support_eq]⟩
  | _, _, _, _, .comp first second =>
      let one := projectCell first
      let two := projectCell second
      ⟨.comp one.cell two.cell, by simp only [PresentedCell.support, one.support_eq, two.support_eq]⟩
  | _, _, _, _, .inverse child =>
      let one := projectCell child
      ⟨.inverse one.cell, one.support_eq⟩
  | _, _, _, _, .assoc p q r =>
      ⟨.assoc (expandTrack p) (expandTrack q) (expandTrack r), by simp only [PresentedCell.support, expandTrack_support]⟩
  | _, _, _, _, .leftUnit p => ⟨.leftUnit (expandTrack p), expandTrack_support p⟩
  | _, _, _, _, .rightUnit p => ⟨.rightUnit (expandTrack p), expandTrack_support p⟩
  | _, _, _, _, .leftInv p => ⟨.leftInv (expandTrack p), expandTrack_support p⟩
  | _, _, _, _, .rightInv p => ⟨.rightInv (expandTrack p), expandTrack_support p⟩

theorem projectCell_support {a b} {p q : Circuit signature a b}
    {first second : RewriteTrack (relators := rules) p q} (cell : Cell first second) :
    PresentedCell.support (projectCell cell).cell = PresentedCell.support cell := (projectCell cell).support_eq

end CryptoLogic.Polygraph.MixedCircuit.Examples.MAC.Structural.Fusion
