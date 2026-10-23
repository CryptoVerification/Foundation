import Foundation.Crypto.Semantics.Oracle.StatefulDiagramHeadPull

/-! Derived local cells for pulling a head across checked exchanges.
Only existing involution, self, braid and horizontal interchange are used;
this module introduces no new higher generator. -/
set_option backward.isDefEq.respectTransparency false

namespace CryptoOracle.StatefulDiagram
variable {Slot Op : Type} [DecidableEq Slot]

/-- Primitive checked exchange at the head of a word. -/
def frontSwap (signature : Op → Interface Slot) (a b : Op) (future : List Op)
    (accepted : checkExchange signature a b = true) :
    Exchange signature (a :: b :: future) (b :: a :: future) := .swap [] future a b accepted

/-- Two opposite head swaps contract by the old bounded involution cell. -/
def frontInvolution (signature : Op → Interface Slot) (a b : Op) (future : List Op)
    (ab : checkExchange signature a b = true) (ba : checkExchange signature b a = true) :
    HorizontalCoherence signature
      (.trans (frontSwap signature a b future ab) (frontSwap signature b a future ba))
      (.refl (a :: b :: future)) := by
  simpa [frontSwap, swapTwice, Exchange.suffix, Exchange.whisker, List.nil_append,
    List.append_nil, List.cons_append] using
    HorizontalCoherence.suffix future (.base (.local (.original (.involution a b ab ba))))

/-- The repeated-ID self-loop contracts using the explicit earlier self cell. -/
def frontSelf (signature : Op → Interface Slot) (a : Op) (future : List Op)
    (accepted : checkExchange signature a a = true) :
    HorizontalCoherence signature (frontSwap signature a a future accepted) (.refl (a :: a :: future)) := by
  simpa [frontSwap, Exchange.suffix, Exchange.whisker, List.nil_append,
    List.append_nil, List.cons_append] using
    HorizontalCoherence.suffix future (.base (.local (.self a accepted)))

/-- The three-operation overlap, with the actual common suffix retained. -/
def frontBraid (signature : Op → Interface Slot) (a b c : Op) (future : List Op)
    (ab : checkExchange signature a b = true) (ac : checkExchange signature a c = true)
    (bc : checkExchange signature b c = true) :
    HorizontalCoherence signature
      (.trans (frontSwap signature a b (c :: future) ab)
        (.trans ((frontSwap signature a c future ac).prepend signature b) (frontSwap signature b c (a :: future) bc)))
      (.trans ((frontSwap signature b c future bc).prepend signature a)
        (.trans (frontSwap signature a c (b :: future) ac) ((frontSwap signature a b future ab).prepend signature c))) := by
  simpa [frontSwap, braidLeft, braidRight, Exchange.suffix, Exchange.whisker, Exchange.prepend,
    List.nil_append, List.append_nil, List.cons_append] using
    HorizontalCoherence.suffix future (.base (.local (.original (.braid a b c ab ac bc))))

/-- Move an arbitrary tail transformation past a head exchange. This is the
separated case of head-extraction naturality, derived from horizontal
interchange rather than assumed as another primitive root. -/
def frontSwap_tail (signature : Op → Interface Slot) (a b : Op)
    (accepted : checkExchange signature a b = true) {one two : List Op}
    (path : Exchange signature one two) :
    HorizontalCoherence signature
      (.trans ((path.prepend signature b).prepend signature a) (frontSwap signature a b two accepted))
      (.trans (frontSwap signature a b one accepted) ((path.prepend signature a).prepend signature b)) := by
  simpa [horizontalLeft, horizontalRight, frontSwap, Exchange.prefix, Exchange.suffix, Exchange.whisker,
    List.nil_append, List.append_nil, List.cons_append] using
    (horizontalInterchange signature (Exchange.swap [] [] a b accepted) path).symm

end CryptoOracle.StatefulDiagram
