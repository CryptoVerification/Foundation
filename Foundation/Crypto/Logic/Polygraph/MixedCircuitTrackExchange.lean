import Foundation.Crypto.Logic.Polygraph.MixedCircuitHigher
import Foundation.Logic.Polygraph.FourNaturality

/-! Exchange of a single actual rewrite with an arbitrary proof track in the
other factor. Derived from separated single-step squares and groupoid laws;
no whole-track exchange generator is added. Inverse is proof reversal only. -/
namespace CryptoLogic.Polygraph.MixedCircuit.TrackExchange
open Foundation.Logic.Polygraph
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}
set_option backward.isDefEq.respectTransparency false

def separated {a b} {p q r : Circuit signature a b}
    {first : Step relators p q} {second : Step relators p r} (apart : Separated first second) :
    Homotopy (.comp (.step first) (.step apart.diamond.afterFirst))
      (.comp (.step second) (.step apart.diamond.afterSecond)) :=
  (Four.comp (.refl (.step first)) (Four.rightUnit (.step apart.diamond.afterFirst))).symm.trans
    ((Four.generator (.separated apart)).trans
      (Four.comp (.refl (.step second)) (Four.rightUnit (.step apart.diamond.afterSecond))))

def seqRight {a b c} {p p' : Circuit signature a b} (change : Step relators p p')
    {q q' : Circuit signature b c} (path : RewriteTrack (relators := relators) q q') :
    Homotopy (.comp ((Placement.seqRight p).track path) (.step (.seqLeft change q')))
      (.comp (.step (.seqLeft change q)) ((Placement.seqRight p').track path)) :=
  FourNaturality.natural (fun x => Circuit.seq p x) (fun x => Circuit.seq p' x)
    (fun edge => Step.seqRight p edge) (fun edge => Step.seqRight p' edge)
    (fun x => .step (.seqLeft change x))
    (fun edge => (separated (.seqLR change edge)).symm) path

def seqLeft {a b c} {q q' : Circuit signature b c} (change : Step relators q q')
    {p p' : Circuit signature a b} (path : RewriteTrack (relators := relators) p p') :
    Homotopy (.comp ((Placement.seqLeft q).track path) (.step (.seqRight p' change)))
      (.comp (.step (.seqRight p change)) ((Placement.seqLeft q').track path)) :=
  FourNaturality.natural (fun x => Circuit.seq x q) (fun x => Circuit.seq x q')
    (fun edge => Step.seqLeft edge q) (fun edge => Step.seqLeft edge q')
    (fun x => .step (.seqRight x change))
    (fun edge => separated (.seqLR edge change)) path

def tensorRight {a b c d} {p p' : Circuit signature a b} (change : Step relators p p')
    {q q' : Circuit signature c d} (path : RewriteTrack (relators := relators) q q') :
    Homotopy (.comp ((Placement.tensorRight p).track path) (.step (.tensorLeft change q')))
      (.comp (.step (.tensorLeft change q)) ((Placement.tensorRight p').track path)) :=
  FourNaturality.natural (fun x => Circuit.tensor p x) (fun x => Circuit.tensor p' x)
    (fun edge => Step.tensorRight p edge) (fun edge => Step.tensorRight p' edge)
    (fun x => .step (.tensorLeft change x))
    (fun edge => (separated (.tensorLR change edge)).symm) path

def tensorLeft {a b c d} {q q' : Circuit signature c d} (change : Step relators q q')
    {p p' : Circuit signature a b} (path : RewriteTrack (relators := relators) p p') :
    Homotopy (.comp ((Placement.tensorLeft q).track path) (.step (.tensorRight p' change)))
      (.comp (.step (.tensorRight p change)) ((Placement.tensorLeft q').track path)) :=
  FourNaturality.natural (fun x => Circuit.tensor x q) (fun x => Circuit.tensor x q')
    (fun edge => Step.tensorLeft edge q) (fun edge => Step.tensorLeft edge q')
    (fun x => .step (.tensorRight x change))
    (fun edge => separated (.tensorLR edge change)) path

end CryptoLogic.Polygraph.MixedCircuit.TrackExchange
