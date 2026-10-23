import Foundation.Logic.Polygraph.StructuralCartesianOneHole

/-! Four projection argument diagrams with bookkeeping removed. These use
only the existing single-step argument naturality and groupoid laws, including
the two erased argument sites. No new product critical generator is needed. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProductProjectionNaturality
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

def forkLeft {a b c : Shape Atom} {p p' : Wire a b} (change : Step p p') (q : Wire a c) : Step (fork p q) (fork p' q) :=
  .seqRight (.copy a) (.tensorLeft change q)

def forkRight {a b c : Shape Atom} (p : Wire a b) {q q' : Wire a c} (change : Step q q') : Step (fork p q) (fork p q') :=
  .seqRight (.copy a) (.tensorRight p change)

def fstLeft {a b c : Shape Atom} {p p' : Wire a b} (change : Step p p') (q : Wire a c) :
    Homotopy
      (.comp (.step (.seqLeft (forkLeft change q) (fst b c))) (.step (.root (.betaFst p' q))))
      (.comp (.step (.root (.betaFst p q))) (.step change)) :=
  (Four.comp ((CategoryCritical.Context.seqLeft
    (.seqRight (.copy a) (.tensorLeft .hole q)) (fst b c)).changeCell change).symm (.refl _)).trans
      (argumentCell (.betaFstFirst q) change)

def fstRight {a b c : Shape Atom} (p : Wire a b) {q q' : Wire a c} (change : Step q q') :
    Homotopy
      (.comp (.step (.seqLeft (forkRight p change) (fst b c))) (.step (.root (.betaFst p q'))))
      (.step (.root (.betaFst p q))) :=
  (Four.comp ((CategoryCritical.Context.seqLeft
    (.seqRight (.copy a) (.tensorRight p .hole)) (fst b c)).changeCell change).symm (.refl _)).trans
      ((argumentCell (.betaFstLast p) change).trans (Four.rightUnit _))

def sndLeft {a b c : Shape Atom} {p p' : Wire a b} (change : Step p p') (q : Wire a c) :
    Homotopy
      (.comp (.step (.seqLeft (forkLeft change q) (snd b c))) (.step (.root (.betaSnd p' q))))
      (.step (.root (.betaSnd p q))) :=
  (Four.comp ((CategoryCritical.Context.seqLeft
    (.seqRight (.copy a) (.tensorLeft .hole q)) (snd b c)).changeCell change).symm (.refl _)).trans
      ((argumentCell (.betaSndFirst q) change).trans (Four.rightUnit _))

def sndRight {a b c : Shape Atom} (p : Wire a b) {q q' : Wire a c} (change : Step q q') :
    Homotopy
      (.comp (.step (.seqLeft (forkRight p change) (snd b c))) (.step (.root (.betaSnd p q'))))
      (.comp (.step (.root (.betaSnd p q))) (.step change)) :=
  (Four.comp ((CategoryCritical.Context.seqLeft
    (.seqRight (.copy a) (.tensorRight p .hole)) (snd b c)).changeCell change).symm (.refl _)).trans
      (argumentCell (.betaSndLast p) change)

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProductProjectionNaturality
