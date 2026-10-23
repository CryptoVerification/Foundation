import Foundation.Crypto.Semantics.Oracle.StatefulDiagramSelfExchange

/-! Structural groupoid laws for raw Exchange proof terms. They supplement
local exchange higher diagrams; no arbitrary-parallel-path rule is introduced
and global coherence remains a separate theorem. -/
namespace CryptoOracle.StatefulDiagram
variable {Slot Op : Type} [DecidableEq Slot]

inductive ExchangeCoherence (signature : Op → Interface Slot) : {one two : List Op} →
    Exchange signature one two → Exchange signature one two → Type where
  | local {one two} {p q : Exchange signature one two} :
      ExchangeHigherWithSelf signature p q → ExchangeCoherence signature p q
  | refl {one two} (p : Exchange signature one two) : ExchangeCoherence signature p p
  | symm {one two} {p q : Exchange signature one two} : ExchangeCoherence signature p q → ExchangeCoherence signature q p
  | trans {one two} {p q r : Exchange signature one two} :
      ExchangeCoherence signature p q → ExchangeCoherence signature q r → ExchangeCoherence signature p r
  | comp {one two three} {p p' : Exchange signature one two} {q q' : Exchange signature two three} :
      ExchangeCoherence signature p p' → ExchangeCoherence signature q q' →
        ExchangeCoherence signature (.trans p q) (.trans p' q')
  | inverse {one two} {p q : Exchange signature one two} :
      ExchangeCoherence signature p q → ExchangeCoherence signature (.symm p) (.symm q)
  | whisker {one two} {p q : Exchange signature one two} (past future : List Op) :
      ExchangeCoherence signature p q → ExchangeCoherence signature
        (p.whisker signature past future) (q.whisker signature past future)
  | assoc {a b c d} (p : Exchange signature a b) (q : Exchange signature b c) (r : Exchange signature c d) :
      ExchangeCoherence signature (.trans (.trans p q) r) (.trans p (.trans q r))
  | leftUnit {a b} (p : Exchange signature a b) : ExchangeCoherence signature (.trans (.refl a) p) p
  | rightUnit {a b} (p : Exchange signature a b) : ExchangeCoherence signature (.trans p (.refl b)) p
  | leftInv {a b} (p : Exchange signature a b) : ExchangeCoherence signature (.trans (.symm p) p) (.refl b)
  | rightInv {a b} (p : Exchange signature a b) : ExchangeCoherence signature (.trans p (.symm p)) (.refl a)
  | inverseRefl (a) : ExchangeCoherence signature (.symm (.refl a)) (.refl a)
  | inverseInverse {a b} (p : Exchange signature a b) : ExchangeCoherence signature (.symm (.symm p)) p
  | inverseComp {a b c} (p : Exchange signature a b) (q : Exchange signature b c) :
      ExchangeCoherence signature (.symm (.trans p q)) (.trans (.symm q) (.symm p))

def undoSuffix (signature : Op → Interface Slot) {a b c : List Op}
    (p : Exchange signature a b) (q : Exchange signature b c) :
    ExchangeCoherence signature (.trans (.trans p q) (.symm q)) p :=
  (ExchangeCoherence.assoc p q (.symm q)).trans
    ((ExchangeCoherence.comp (.refl p) (.rightInv q)).trans (.rightUnit p))

def cancelSuffix (signature : Op → Interface Slot) {a b c : List Op}
    {p q : Exchange signature a b} (r : Exchange signature b c)
    (cell : ExchangeCoherence signature (.trans p r) (.trans q r)) : ExchangeCoherence signature p q :=
  (undoSuffix signature p r).symm.trans
    ((ExchangeCoherence.comp cell (.refl (.symm r))).trans (undoSuffix signature q r))

/-- Remove a path followed by its inverse on the left of a residual path. -/
def undoPrefix (signature : Op → Interface Slot) {a b c : List Op}
    (p : Exchange signature a b) (q : Exchange signature b c) :
    ExchangeCoherence signature (.trans (.symm p) (.trans p q)) q :=
  (ExchangeCoherence.assoc (.symm p) p q).symm.trans
    ((ExchangeCoherence.comp (.leftInv p) (.refl q)).trans (.leftUnit q))

def cancelPrefix (signature : Op → Interface Slot) {a b c : List Op}
    (r : Exchange signature a b) {p q : Exchange signature b c}
    (cell : ExchangeCoherence signature (.trans r p) (.trans r q)) :
    ExchangeCoherence signature p q :=
  (undoPrefix signature r p).symm.trans
    ((ExchangeCoherence.comp (.refl (.symm r)) cell).trans (undoPrefix signature r q))

/-- Cancellation is reversible; no arbitrary parallel-path generator is used. -/
theorem common_suffix_iff (signature : Op → Interface Slot) {a b c : List Op}
    (p q : Exchange signature a b) (r : Exchange signature b c) :
    Nonempty (ExchangeCoherence signature (.trans p r) (.trans q r)) ↔
      Nonempty (ExchangeCoherence signature p q) := by
  constructor
  · rintro ⟨cell⟩
    exact ⟨cancelSuffix signature r cell⟩
  · rintro ⟨cell⟩
    exact ⟨.comp cell (.refl r)⟩

theorem common_prefix_iff (signature : Op → Interface Slot) {a b c : List Op}
    (r : Exchange signature a b) (p q : Exchange signature b c) :
    Nonempty (ExchangeCoherence signature (.trans r p) (.trans r q)) ↔
      Nonempty (ExchangeCoherence signature p q) := by
  constructor
  · rintro ⟨cell⟩
    exact ⟨cancelPrefix signature r cell⟩
  · rintro ⟨cell⟩
    exact ⟨.comp (.refl r) cell⟩

end CryptoOracle.StatefulDiagram
