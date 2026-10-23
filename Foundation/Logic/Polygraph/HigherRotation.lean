import Foundation.Logic.Polygraph.Higher

/-! Rotate explicitly supplied higher squares using only proof-groupoid laws.
No cancellation of stochastic continuations is asserted. -/
namespace Foundation.Logic.Polygraph.Four
universe u v w
variable {A : Type u} {R : A → A → Type v}
variable {G : {a b : A} → Track R a b → Track R a b → Type w}

def stripLeft {a b c : A} (head : Track R a b) {p : Track R a c} {q : Track R b c}
    (square : Four G p (.comp head q)) : Four G (.comp (.inv head) p) q :=
  (Four.comp (.refl (.inv head)) square).trans
    ((Four.assoc (.inv head) head q).symm.trans
      ((Four.comp (Four.leftInv head) (.refl q)).trans (Four.leftUnit q)))

def divideRight {a b c : A} (suffix : Track R b c) {p : Track R a b} {q : Track R a c}
    (square : Four G (.comp p suffix) q) : Four G p (.comp q (.inv suffix)) :=
  (Four.rightUnit p).symm.trans
    ((Four.comp (.refl p) (Four.rightInv suffix).symm).trans
      ((Four.assoc p suffix (.inv suffix)).symm.trans (Four.comp square (.refl (.inv suffix)))))

def rotate {a b c d : A} (p : Track R a b) (q : Track R b d) (r : Track R a c) (s : Track R c d)
    (square : Four G (.comp p q) (.comp r s)) : Four G (.comp (.inv r) p) (.comp s (.inv q)) :=
  divideRight q ((Four.assoc (.inv r) p q).trans (stripLeft r square))

end Foundation.Logic.Polygraph.Four
