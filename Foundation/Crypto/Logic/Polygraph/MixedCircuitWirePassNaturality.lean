import Foundation.Crypto.Logic.Polygraph.MixedCircuitWireNormalization
import Foundation.Crypto.Logic.Polygraph.MixedCircuitTrackExchange

/-! From checked single-root compatibility to a generated higher square in
every mixed context. Only the root contracts are inputs; the whole-context
comparison is constructed using separated exchange and proof-groupoid laws.
This interface has single-step residuals and is not a completion theorem. -/
namespace CryptoLogic.Polygraph.MixedCircuit.Stateful.WiringUnion.WirePass
open Foundation.Logic.Polygraph
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {original : Rule → Relator signature}
set_option backward.isDefEq.respectTransparency false

structure RootCompatibility (original : Rule → Relator signature) where
  residual : (label : Rule) → Step (rules original) (output (original label).left) (output (original label).right)
  square : (label : Rule) →
    Homotopy (.comp (.step (embedStep (.root (.rule label)))) (witness (original label).right))
      (.comp (witness (original label).left) (.step (residual label)))
  support_eq : (label : Rule) → (residual label).support = (Primitive.rule (relators := original) label).support

def residual (contract : RootCompatibility original) : {a b : Port signature} →
    {p q : Circuit signature a b} → Step original p q → Step (rules original) (output p) (output q)
  | _, _, _, _, .root (.rule label) => contract.residual label
  | _, _, _, _, .seqLeft child fixed => .seqLeft (residual contract child) (output fixed)
  | _, _, _, _, .seqRight fixed child => .seqRight (output fixed) (residual contract child)
  | _, _, _, _, .tensorLeft child fixed => .tensorLeft (residual contract child) (output fixed)
  | _, _, _, _, .tensorRight fixed child => .tensorRight (output fixed) (residual contract child)

theorem residual_support (contract : RootCompatibility original) {a b} {p q : Circuit signature a b}
    (change : Step original p q) : (residual contract change).support = change.support := by
  induction change with
  | root primitive => cases primitive; exact contract.support_eq _
  | seqLeft child fixed ih | seqRight fixed child ih | tensorLeft child fixed ih | tensorRight fixed child ih =>
      simp only [residual, Step.support, output_needs, ih]

def square (contract : RootCompatibility original) : {a b : Port signature} → {p q : Circuit signature a b} →
    (change : Step original p q) →
    Homotopy (.comp (.step (embedStep change)) (witness q))
      (.comp (witness p) (.step (residual contract change)))
  | _, _, _, _, .root (.rule label) => contract.square label
  | _, _, _, _, .seqLeft (a := p) (a' := p') child fixed =>
      (Four.assoc (.step (.seqLeft (embedStep child) fixed))
        ((Placement.seqLeft fixed).track (witness p'))
        ((Placement.seqRight (output p')).track (witness fixed))).symm.trans
      ((Four.comp ((square contract child).whisker (.seqLeft fixed)) (.refl _)).trans
      ((Four.assoc _ _ _).trans
      ((Four.comp (.refl _) (TrackExchange.seqRight (residual contract child) (witness fixed)).symm).trans
        (Four.assoc _ _ _).symm)))
  | _, _, _, _, .seqRight fixed child =>
      (Four.assoc _ _ _).symm.trans
      ((Four.comp (TrackExchange.seqLeft (embedStep child) (witness fixed)).symm (.refl _)).trans
      ((Four.assoc _ _ _).trans
      ((Four.comp (.refl _) ((square contract child).whisker (.seqRight (output fixed)))).trans
        (Four.assoc _ _ _).symm)))
  | _, _, _, _, .tensorLeft (a := p) (a' := p') child fixed =>
      (Four.assoc (.step (.tensorLeft (embedStep child) fixed))
        ((Placement.tensorLeft fixed).track (witness p'))
        ((Placement.tensorRight (output p')).track (witness fixed))).symm.trans
      ((Four.comp ((square contract child).whisker (.tensorLeft fixed)) (.refl _)).trans
      ((Four.assoc _ _ _).trans
      ((Four.comp (.refl _) (TrackExchange.tensorRight (residual contract child) (witness fixed)).symm).trans
        (Four.assoc _ _ _).symm)))
  | _, _, _, _, .tensorRight fixed child =>
      (Four.assoc _ _ _).symm.trans
      ((Four.comp (TrackExchange.tensorLeft (embedStep child) (witness fixed)).symm (.refl _)).trans
      ((Four.assoc _ _ _).trans
      ((Four.comp (.refl _) ((square contract child).whisker (.tensorRight (output fixed)))).trans
        (Four.assoc _ _ _).symm)))

def normalizedTrack (contract : RootCompatibility original) {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := original) p q) : RewriteTrack (relators := rules original) (output p) (output q) :=
  path.map output (fun change => residual contract change)

def trackSquare (contract : RootCompatibility original) {a b} {p q : Circuit signature a b}
    (path : RewriteTrack (relators := original) p q) :
    Homotopy (.comp (embedTrack path) (witness q)) (.comp (witness p) (normalizedTrack contract path)) := by
  have mapped : path.map id (fun change => embedStep change) = embedTrack path := by
    induction path <;> simp_all only [Track.map, embedTrack, id_eq]
  have result : Homotopy
      (.comp (path.map id (fun change => embedStep change)) (witness q))
      (.comp (witness p) (normalizedTrack contract path)) :=
    FourNaturality.natural id output (fun change => embedStep change)
      (fun change => residual contract change) witness (fun change => square contract change) path
  simpa only [mapped] using result

end CryptoLogic.Polygraph.MixedCircuit.Stateful.WiringUnion.WirePass
