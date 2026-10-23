import Foundation.Crypto.Logic.Polygraph.MixedCircuitTrackExchange

/-! Guard accounting for derived track exchange. Reversing a proof square
retains its interior requirements; it does not erase cancelled dependencies. -/
namespace CryptoLogic.Polygraph.MixedCircuit.TrackExchange
open Foundation.Logic.Polygraph
variable {Box Requirement Budget Rule : Type} [DecidableEq Requirement]
variable {signature : Signature Box Requirement Budget} {relators : Rule → Relator signature}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem undoRight_support {a b} {p q r : Circuit signature a b}
    (one : RewriteTrack (relators := relators) p q) (two : RewriteTrack (relators := relators) q r) :
    Homotopy.support (FourNaturality.undoRight one two) = one.support ∪ two.support := by
  simp only [FourNaturality.undoRight, Homotopy.support, RewriteTrack.support]
  ext label
  simp only [Finset.mem_union]
  tauto

theorem undoLeft_support {a b} {p q r : Circuit signature a b}
    (one : RewriteTrack (relators := relators) p q) (two : RewriteTrack (relators := relators) p r) :
    Homotopy.support (FourNaturality.undoLeft one two) = one.support ∪ two.support := by
  simp only [FourNaturality.undoLeft, Homotopy.support, RewriteTrack.support]
  ext label
  simp only [Finset.mem_union]
  tauto

theorem undoInversePrefix_support {a b} {p q r : Circuit signature a b}
    (one : RewriteTrack (relators := relators) p q) (two : RewriteTrack (relators := relators) q r) :
    Homotopy.support (FourNaturality.undoInversePrefix one two) = one.support ∪ two.support := by
  simp only [FourNaturality.undoInversePrefix, Homotopy.support, RewriteTrack.support]
  ext label
  simp only [Finset.mem_union]
  tauto

theorem cancelPrefix_support {a b} {p q r : Circuit signature a b}
    (head : RewriteTrack (relators := relators) p q)
    {one two : RewriteTrack (relators := relators) q r}
    (cell : Homotopy (.comp head one) (.comp head two)) :
    Homotopy.support (FourNaturality.cancelPrefix head cell) = cell.support := by
  simp only [FourNaturality.cancelPrefix, Homotopy.support, undoInversePrefix_support, RewriteTrack.support]
  ext label
  have left : label ∈ head.support ∪ one.support → label ∈ cell.support := fun member => cell.boundaries.1 member
  have right : label ∈ head.support ∪ two.support → label ∈ cell.support := fun member => cell.boundaries.2 member
  simp only [Finset.mem_union] at *
  tauto

theorem invertSquare_support {a b} {p q r s : Circuit signature a b}
    (one : RewriteTrack (relators := relators) p q) (two : RewriteTrack (relators := relators) q s)
    (three : RewriteTrack (relators := relators) p r) (four : RewriteTrack (relators := relators) r s)
    (cell : Homotopy (.comp one two) (.comp three four)) :
    Homotopy.support (FourNaturality.invertSquare one two three four cell) = Homotopy.support cell := by
  rw [FourNaturality.invertSquare, cancelPrefix_support]
  simp only [Homotopy.support, undoLeft_support, undoRight_support, RewriteTrack.support]
  ext label
  have left : label ∈ one.support ∪ two.support → label ∈ cell.support := fun member => cell.boundaries.1 member
  have right : label ∈ three.support ∪ four.support → label ∈ cell.support := fun member => cell.boundaries.2 member
  simp only [Finset.mem_union] at *
  tauto

theorem natural_union (one two fixed fone ftwo gone gtwo start middle finish : Finset Requirement)
    (capOne : fone ⊆ one ∪ fixed) (capTwo : ftwo ⊆ two ∪ fixed)
    (capThree : gone ⊆ one ∪ fixed) (capFour : gtwo ⊆ two ∪ fixed)
    (startBound : start ⊆ one) (middleBound : middle ⊆ one) (finishBound : finish ⊆ two) :
    ((fone ∪ ftwo) ∪ (finish ∪ fixed)) ∪
      ((fone ∪ (two ∪ fixed)) ∪
        (((fone ∪ (middle ∪ fixed)) ∪ gtwo) ∪
          (((one ∪ fixed) ∪ gtwo) ∪ (((start ∪ fixed) ∪ gone) ∪ gtwo)))) = (one ∪ two) ∪ fixed := by
  let target := (one ∪ two) ∪ fixed
  have hOne : one ⊆ target := Finset.subset_union_left.trans Finset.subset_union_left
  have hTwo : two ⊆ target := Finset.subset_union_right.trans Finset.subset_union_left
  have hFixed : fixed ⊆ target := Finset.subset_union_right
  have hStart := startBound.trans hOne
  have hMiddle := middleBound.trans hOne
  have hFinish := finishBound.trans hTwo
  have hFOne := capOne.trans (Finset.union_subset hOne hFixed)
  have hFTwo := capTwo.trans (Finset.union_subset hTwo hFixed)
  have hGOne := capThree.trans (Finset.union_subset hOne hFixed)
  have hGTwo := capFour.trans (Finset.union_subset hTwo hFixed)
  apply Finset.Subset.antisymm
  · change _ ⊆ target
    repeat' first | assumption | apply Finset.union_subset
  · intro label member
    simp only [Finset.mem_union] at member ⊢
    rcases member with (h | h) | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl h)))))
    · exact Or.inr (Or.inl (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr h))

theorem natural_support {SourceRule : Type} {sourceRules : SourceRule → Relator signature} {a b c d : Port signature}
    (f g : Circuit signature a b → Circuit signature c d)
    (mapF : ∀ {p q}, Step sourceRules p q → Step relators (f p) (f q))
    (mapG : ∀ {p q}, Step sourceRules p q → Step relators (g p) (g q))
    (component : ∀ p, RewriteTrack (relators := relators) (f p) (g p))
    (stepSquare : ∀ {p q} (change : Step sourceRules p q),
      Homotopy (.comp (.step (mapF change)) (component q)) (.comp (component p) (.step (mapG change))))
    (fixed : Finset Requirement)
    (firstBound : ∀ {p q} (path : RewriteTrack (relators := sourceRules) p q),
      RewriteTrack.support (path.map f mapF) ⊆ RewriteTrack.support path ∪ fixed)
    (secondBound : ∀ {p q} (path : RewriteTrack (relators := sourceRules) p q),
      RewriteTrack.support (path.map g mapG) ⊆ RewriteTrack.support path ∪ fixed)
    (componentSupport : ∀ p, (component p).support = p.needs ∪ fixed)
    (stepSupport : ∀ {p q} (change : Step sourceRules p q), (stepSquare change).support = change.support ∪ fixed)
    {p q} (path : RewriteTrack (relators := sourceRules) p q) :
    Homotopy.support (FourNaturality.natural f g mapF mapG component stepSquare path) = RewriteTrack.support path ∪ fixed := by
  induction path with
  | refl p => simp only [FourNaturality.natural, Homotopy.support, componentSupport, RewriteTrack.support, Finset.union_self]
  | step change => exact stepSupport change
  | @comp x y z first second one two =>
      simp only [FourNaturality.natural, Homotopy.support, one, two, componentSupport, RewriteTrack.support]
      exact natural_union (RewriteTrack.support first) (RewriteTrack.support second) fixed
        (RewriteTrack.support (first.map f mapF)) (RewriteTrack.support (second.map f mapF))
        (RewriteTrack.support (first.map g mapG)) (RewriteTrack.support (second.map g mapG))
        x.needs y.needs z.needs (firstBound first) (firstBound second) (secondBound first) (secondBound second)
        (RewriteTrack.boundaries first).1 (RewriteTrack.boundaries first).2 (RewriteTrack.boundaries second).2
  | @inv x y child ih =>
      exact (invertSquare_support (child.map f mapF) (component y) (component x) (child.map g mapG)
        (FourNaturality.natural f g mapF mapG component stepSquare child)).trans ih

end CryptoLogic.Polygraph.MixedCircuit.TrackExchange
