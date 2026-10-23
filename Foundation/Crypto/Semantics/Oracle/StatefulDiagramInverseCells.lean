import Foundation.Crypto.Semantics.Oracle.StatefulDiagramPathLaws

/-! Derived inverse cells needed when comparing generated paths. No new
higher root, normalizer-relative rule or arbitrary-parallel-path generator
is added in this module. -/
namespace CryptoOracle.StatefulDiagram
variable {Slot Op : Type} [DecidableEq Slot]

/-- A supplied right-inverse contraction identifies that path with the formal
inverse, using cancellation and existing groupoid laws. -/
def identifyInverse (signature : Op → Interface Slot) {one two : List Op}
    (forward : Exchange signature one two) (backward : Exchange signature two one)
    (contraction : ExchangeCoherence signature (.trans forward backward) (.refl one)) :
    ExchangeCoherence signature backward (.symm forward) :=
  cancelPrefix signature forward (contraction.trans (ExchangeCoherence.rightInv forward).symm)

/-- Reverse-direction primitive exchange agrees, up to explicit higher data,
with the formal inverse. This is derived from the bounded involution cell. -/
def reverseSwapCell (signature : Op → Interface Slot) (a b : Op)
    (ab : checkExchange signature a b = true) (ba : checkExchange signature b a = true) :
    ExchangeCoherence signature (Exchange.swap [] [] b a ba) (.symm (Exchange.swap [] [] a b ab)) :=
  identifyInverse signature (.swap [] [] a b ab) (.swap [] [] b a ba)
    (.local (.original (.involution a b ab ba)))

/-- The derived comparison can be placed inside any common execution context. -/
def reverseSwapCell_context (signature : Op → Interface Slot) (past future : List Op) (a b : Op)
    (ab : checkExchange signature a b = true) (ba : checkExchange signature b a = true) :
    ExchangeCoherence signature
      ((Exchange.swap [] [] b a ba).whisker signature past future)
      ((Exchange.symm (Exchange.swap [] [] a b ab)).whisker signature past future) :=
  (reverseSwapCell signature a b ab ba).whisker past future

/-- Once one orientation contracts, the opposite backtrack contracts without
postulating another inverse rule. -/
def oppositeBacktrack (signature : Op → Interface Slot) {one two : List Op}
    (forward : Exchange signature one two) (backward : Exchange signature two one)
    (contraction : ExchangeCoherence signature (.trans forward backward) (.refl one)) :
    ExchangeCoherence signature (.trans backward forward) (.refl two) :=
  (ExchangeCoherence.comp (identifyInverse signature forward backward contraction) (.refl forward)).trans
    (.leftInv forward)

end CryptoOracle.StatefulDiagram
