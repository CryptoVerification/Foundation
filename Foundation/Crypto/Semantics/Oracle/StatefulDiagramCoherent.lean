import Foundation.Crypto.Semantics.Oracle.StatefulDiagramPullOverlap

/-! Global constructive coherence for the checked exchange fragment, in the
explicit HorizontalCoherence extension. Head deletion reduces word length;
no whole-normalizer or arbitrary-parallel-path higher root is assumed.
Copy/discard and arbitrary cryptographic-box transformations are not covered. -/
set_option backward.isDefEq.respectTransparency false
namespace CryptoOracle.StatefulDiagram
variable {Slot Op : Type} [DecidableEq Slot] [DecidableEq Op]

/-- The empty-word reference path, transported to the supplied endpoints. -/
def emptyReference (signature : Op → Interface Slot) (one two : List Op)
    (source : one = []) (target : two = []) : Exchange signature one two := by
  subst one
  subst two
  exact .refl []

/-- Contract every path on empty words by structural laws. Primitive swaps
cannot have an empty source, as witnessed by their word lengths. -/
def emptyContraction (signature : Op → Interface Slot) : {one two : List Op} →
    (path : Exchange signature one two) → (source : one = []) → (target : two = []) →
    HorizontalCoherence signature path (emptyReference signature one two source target)
  | _, _, .refl _, source, target => by
    cases source
    simpa only [emptyReference] using HorizontalCoherence.refl (Exchange.refl (signature := signature) [])
  | _, _, .swap past future a b accepted, source, _ => by
    have length := congrArg List.length source
    simp only [List.length_append, List.length_cons, List.length_nil] at length
    exact False.elim (by omega)
  | _, _, .symm child, source, target => by
    have cell := emptyContraction signature child target source
    cases source
    cases target
    simp only [emptyReference] at cell ⊢
    exact (HorizontalCoherence.inverse cell).trans (.base (.inverseRefl []))
  | _, _, .trans first second, source, target => by
    have middle := List.length_eq_zero_iff.mp
      ((first.length_eq signature).symm.trans (congrArg List.length source))
    have lhs := emptyContraction signature first source middle
    have rhs := emptyContraction signature second middle target
    cases source
    cases middle
    cases target
    simp only [emptyReference] at lhs rhs ⊢
    exact (HorizontalCoherence.comp lhs rhs).trans (.base (.leftUnit (.refl [])))

/-- Common suffix cancellation, derived inside the extended relation. -/
def HorizontalCoherence.cancelSuffix (signature : Op → Interface Slot) {a b c : List Op}
    {p q : Exchange signature a b} (r : Exchange signature b c)
    (cell : HorizontalCoherence signature (.trans p r) (.trans q r)) : HorizontalCoherence signature p q :=
  (HorizontalCoherence.undoSuffix signature p r).symm.trans
    ((HorizontalCoherence.comp cell (.refl (.symm r))).trans (HorizontalCoherence.undoSuffix signature q r))

/-- Construct a higher comparison for ANY parallel checked exchange paths.
At a nonempty source, delete its first label from both paths, recursively
compare residual paths, prefix the result, and cancel the common head pull. -/
def exchangeCoherent (signature : Op → Interface Slot) : {one two : List Op} →
    (p q : Exchange signature one two) → HorizontalCoherence signature p q
  | [], two, p, q => by
    have empty : two = [] := List.length_eq_zero_iff.mp (p.length_eq signature).symm
    exact (emptyContraction signature p rfl empty).trans (emptyContraction signature q rfl empty).symm
  | head :: rest, two, p, q => by
    let source : AccessibleHead signature head (head :: rest) := Or.inl rfl
    let target : AccessibleHead signature head two := (p.accessibleHead_iff signature head).mp source
    let pull := pullHead signature head two target
    let ep := p.eraseData signature head
    let eq := q.eraseData signature head
    have first := pullNaturality signature head p source target
    have second := pullNaturality signature head q source target
    have residual := exchangeCoherent signature ep eq
    have lifted : HorizontalCoherence signature (ep.prepend signature head) (eq.prepend signature head) := by
      simpa only [Exchange.prefix] using HorizontalCoherence.prefix [head] residual
    have middle := HorizontalCoherence.comp (HorizontalCoherence.refl (pullHead signature head (head :: rest) source)) lifted
    have joint : HorizontalCoherence signature (.trans p pull) (.trans q pull) :=
      first.trans (middle.trans second.symm)
    exact HorizontalCoherence.cancelSuffix signature pull joint
termination_by one _ _ _ => one.length
decreasing_by simp only [List.erase_cons_head, List.length_cons]; exact Nat.lt_succ_self _

/-- Existence follows from the explicit computable constructor. -/
theorem exchange_coherence_complete (signature : Op → Interface Slot) {one two : List Op}
    (p q : Exchange signature one two) : Nonempty (HorizontalCoherence signature p q) :=
  ⟨exchangeCoherent signature p q⟩

/-- The source canonical certificate, with its target transported to the
common canonical word. The supplied path is used only to justify that target. -/
def canonicalTargetRoute [LinearOrder Op] (signature : Op → Interface Slot) {one two : List Op}
    (path : Exchange signature one two) : Exchange signature one (canonicalWord signature two) :=
  Eq.mp (congrArg (Exchange signature one) (path.canonicalWord_eq signature)) (canonicalCertificate signature one)

/-- Factor an arbitrary path through canonicalization, with the comparison
expanded by exchangeCoherent into existing higher constructors. This is a
derived diagram, not a new normalizer-relative higher generator. -/
def canonicalFactor [LinearOrder Op] (signature : Op → Interface Slot) {one two : List Op}
    (path : Exchange signature one two) :
    HorizontalCoherence signature (.trans path (canonicalCertificate signature two))
      (canonicalTargetRoute signature path) :=
  exchangeCoherent signature _ _

end CryptoOracle.StatefulDiagram
