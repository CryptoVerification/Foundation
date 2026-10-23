import Foundation.Logic.Polygraph.StructuralCartesianOneHole
import Foundation.Logic.Polygraph.StructuralCartesianTrackNaturality

/-! Derived tensor path calculus. Separated one-step exchanges generate the
exchange of arbitrary finite tracks, including formal proof inverses. No new
higher generator or normalization square is introduced. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProductTracks
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

abbrev Cell {a b : Shape Atom} {p q : Wire a b} (first second : ProofTrack p q) := Homotopy first second

def exchangeStep {a b c d : Shape Atom} {p p' : Wire a b} {q q' : Wire c d}
    (first : Step p p') (second : ProofTrack q q') :
    Cell (.comp (.step (.tensorLeft first q)) (tensorRightTrack p' second))
      (.comp (tensorRightTrack p second) (.step (.tensorLeft first q'))) :=
  (FourNaturality.natural _ _ (fun e => Step.tensorRight p e) (fun e => Step.tensorRight p' e)
    (fun w => Track.step (Step.tensorLeft first w))
    (fun e => (Four.generator (Generator.tensorExchange first e)).symm) second).symm

def exchange {a b c d : Shape Atom} {p p' : Wire a b} {q q' : Wire c d}
    (first : ProofTrack p p') (second : ProofTrack q q') :
    Cell (.comp (tensorLeftTrack q first) (tensorRightTrack p' second))
      (.comp (tensorRightTrack p second) (tensorLeftTrack q' first)) :=
  FourNaturality.natural _ _ (fun e => Step.tensorLeft e q) (fun e => Step.tensorLeft e q')
    (fun w => tensorRightTrack w second) (fun e => exchangeStep e second) first

theorem exchangeStep_generatorCount {a b c d : Shape Atom} {p p' : Wire a b} {q q' : Wire c d}
    (first : Step p p') (second : ProofTrack q q') :
    Homotopy.generatorCount (exchangeStep first second) = stepCount second := by
  unfold exchangeStep
  induction second with
  | refl => rfl
  | step => rfl
  | comp one two ih₁ ih₂ =>
      simp only [FourNaturality.natural, Homotopy.generatorCount, stepCount] at *
      omega
  | inv child ih =>
      simpa only [FourNaturality.natural, Homotopy.generatorCount,
        Homotopy.invertSquare_generatorCount, stepCount] using ih

theorem exchange_generatorCount {a b c d : Shape Atom} {p p' : Wire a b} {q q' : Wire c d}
    (first : ProofTrack p p') (second : ProofTrack q q') :
    Homotopy.generatorCount (exchange first second) = stepCount first * stepCount second := by
  unfold exchange
  induction first with
  | refl => simp only [FourNaturality.natural, Homotopy.generatorCount, stepCount, Nat.zero_mul, Nat.add_zero]
  | step change => simpa only [FourNaturality.natural, stepCount, Nat.one_mul] using exchangeStep_generatorCount change second
  | comp one two ih₁ ih₂ =>
      simp only [FourNaturality.natural, Homotopy.generatorCount, stepCount, Nat.add_mul] at *
      omega
  | inv child ih =>
      simpa only [FourNaturality.natural, Homotopy.generatorCount,
        Homotopy.invertSquare_generatorCount, stepCount] using ih

def tensor {a b c d : Shape Atom} {p p' : Wire a b} {q q' : Wire c d}
    (first : ProofTrack p p') (second : ProofTrack q q') : ProofTrack (.tensor p q) (.tensor p' q') :=
  .comp (tensorLeftTrack q first) (tensorRightTrack p' second)

def tensorCells {a b c d : Shape Atom} {p p' : Wire a b} {q q' : Wire c d}
    {one one' : ProofTrack p p'} {two two' : ProofTrack q q'}
    (first : Cell one one') (second : Cell two two') : Cell (tensor one two) (tensor one' two') :=
  .comp (first.whisker (.tensorLeft q)) (second.whisker (.tensorRight p'))

private def interchange {A : Type} {R : A → A → Type}
    {G : {a b : A} → Track R a b → Track R a b → Type}
    {a b c d e f : A} (one : Track R a b) (two : Track R b c) (three : Track R c d)
    (two' : Track R b e) (three' : Track R e d) (four : Track R d f)
    (middle : Four G (.comp two three) (.comp two' three')) :
    Four G (.comp (.comp one two) (.comp three four))
      (.comp (.comp one two') (.comp three' four)) :=
  (Four.assoc _ _ _).trans
    ((Four.comp (.refl _) (Four.assoc _ _ _).symm).trans
      ((Four.comp (.refl _) (Four.comp middle (.refl _))).trans
        ((Four.comp (.refl _) (Four.assoc _ _ _)).trans (Four.assoc _ _ _).symm)))

def tensorComp {a b c d : Shape Atom} {p p' p'' : Wire a b} {q q' q'' : Wire c d}
    (one : ProofTrack p p') (two : ProofTrack p' p'')
    (three : ProofTrack q q') (four : ProofTrack q' q'') :
    Cell (tensor (.comp one two) (.comp three four)) (.comp (tensor one three) (tensor two four)) :=
  interchange (tensorLeftTrack q one) (tensorLeftTrack q two) (tensorRightTrack p'' three)
    (tensorRightTrack p' three) (tensorLeftTrack q' two) (tensorRightTrack p'' four) (exchange two three)

private def inverseComp {A : Type} {R : A → A → Type}
    {G : {a b : A} → Track R a b → Track R a b → Type}
    {a b c : A} (one : Track R a b) (two : Track R b c) :
    Four G (.inv (.comp one two)) (.comp (.inv two) (.inv one)) :=
  FourNaturality.cancelPrefix (.comp one two)
    ((Four.rightInv _).trans
      ((Four.assoc _ _ _).trans
        ((Four.comp (.refl _) (FourNaturality.undoLeft two (.inv one))).trans (Four.rightInv one))).symm)

def tensorInverse {a b c d : Shape Atom} {p p' : Wire a b} {q q' : Wire c d}
    (first : ProofTrack p p') (second : ProofTrack q q') :
    Cell (tensor (.inv first) (.inv second)) (.inv (tensor first second)) :=
  (exchange (.inv first) (.inv second)).trans (inverseComp _ _).symm

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProductTracks

namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProductTracks
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

def firstProjection {a b c : Shape Atom} {p q : Wire a (.pair b c)} (path : ProofTrack p q) :=
  seqLeftTrack (fst b c) path

def secondProjection {a b c : Shape Atom} {p q : Wire a (.pair b c)} (path : ProofTrack p q) :=
  seqLeftTrack (snd b c) path

def diagonal {a b c : Shape Atom} {p q : Wire a (.pair b c)} (path : ProofTrack p q) :=
  FourPathNaturality.replace (fun w : Wire a (.pair b c) => Wire.tensor (.seq w (fst b c)) (.seq w (snd b c)))
    (fun e => tensor (.step (.seqLeft e (fst b c))) (.step (.seqLeft e (snd b c)))) path

def diagonalSplit {a b c : Shape Atom} : {p q : Wire a (.pair b c)} → (path : ProofTrack p q) →
    Cell (diagonal path) (tensor (firstProjection path) (secondProjection path))
  | _, _, .refl _ => (Four.leftUnit _).symm
  | _, _, .step _ => .refl _
  | _, _, .comp one two =>
      (Four.comp (diagonalSplit one) (diagonalSplit two)).trans (tensorComp (firstProjection one) (firstProjection two)
        (secondProjection one) (secondProjection two)).symm
  | _, _, .inv child =>
      (Four.inverse (diagonalSplit child)).trans (tensorInverse (firstProjection child) (secondProjection child)).symm

def etaEdge {a b c : Shape Atom} {p q : Wire a (.pair b c)} (change : Step p q) :
    Cell ((Variation.eta a b c).left.change change)
      (seqRightTrack (.copy a) (diagonal (.step change))) :=
  (Four.leftUnit _).trans
    ((tensorCells
      ((CategoryCritical.Context.seqLeft .hole (fst b c)).changeCell change)
      ((CategoryCritical.Context.seqLeft .hole (snd b c)).changeCell change)).whisker (.seqRight (.copy a)))

private def replaceCell {A B : Type} {R : A → A → Type} {S : B → B → Type}
    {G : {a b : B} → Track S a b → Track S a b → Type}
    (f : A → B) (one two : ∀ {a b}, R a b → Track S (f a) (f b))
    (cells : ∀ {a b} (e : R a b), Four G (one e) (two e)) :
    {a b : A} → (path : Track R a b) →
    Four G (FourPathNaturality.replace f one path) (FourPathNaturality.replace f two path)
  | _, _, .refl _ => .refl _
  | _, _, .step e => cells e
  | _, _, .comp first second => .comp (replaceCell f one two cells first) (replaceCell f one two cells second)
  | _, _, .inv child => .inverse (replaceCell f one two cells child)

private theorem map_replace {A B C : Type} {R : A → A → Type} {S : B → B → Type} {T : C → C → Type}
    (f : A → B) (edge : ∀ {a b}, R a b → Track S (f a) (f b))
    (g : B → C) (mapEdge : ∀ {a b}, S a b → T (g a) (g b))
    {a b} (path : Track R a b) :
    (FourPathNaturality.replace f edge path).map g mapEdge =
      FourPathNaturality.replace (fun x => g (f x)) (fun e => (edge e).map g mapEdge) path := by
  induction path <;> simp_all only [FourPathNaturality.replace, Track.map]

def etaSplit {a b c : Shape Atom} {p q : Wire a (.pair b c)} (path : ProofTrack p q) :
    Cell ((Variation.eta a b c).left.track path)
      (seqRightTrack (.copy a) (tensor (firstProjection path) (secondProjection path))) := by
  have trim := replaceCell (Variation.eta a b c).left.apply
    (fun e => (Variation.eta a b c).left.change e)
    (fun e => seqRightTrack (.copy a) (diagonal (.step e))) (fun e => etaEdge e) path
  have mapped : FourPathNaturality.replace (Variation.eta a b c).left.apply
      (fun e => seqRightTrack (.copy a) (diagonal (.step e))) path =
      seqRightTrack (.copy a) (diagonal path) := (map_replace
        (fun w : Wire a (.pair b c) => Wire.tensor (.seq w (fst b c)) (.seq w (snd b c)))
        (fun e => tensor (.step (.seqLeft e (fst b c))) (.step (.seqLeft e (snd b c))))
        (fun w => Wire.seq (.copy a) w) (fun e => Step.seqRight (.copy a) e) path).symm
  exact (mapped ▸ trim).trans ((diagonalSplit path).whisker (.seqRight (.copy a)))

private theorem holeTrack {a b : Shape Atom} {p q : Wire a b} (path : ProofTrack p q) :
    (Template.hole : Template a b a b).track path = path := by
  induction path <;> simp_all only [Template.track, FourPathNaturality.replace, Template.change, Template.apply]

/-- Comparison by product observations, derived using eta naturality and
separated exchanges. The hypotheses concern actual proof paths after fst/snd,
not equality of denotations or an arbitrary whole-path generator. -/
def reflect {a b c : Shape Atom} {p q : Wire a (.pair b c)} (first second : ProofTrack p q)
    (left : Cell (firstProjection first) (firstProjection second))
    (right : Cell (secondProjection first) (secondProjection second)) : Cell first second := by
  have observed : Cell ((Variation.eta a b c).left.track first) ((Variation.eta a b c).left.track second) :=
    (etaSplit first).trans
      (((tensorCells left right).whisker (.seqRight (.copy a))).trans (etaSplit second).symm)
  have naturalFirst := argumentTrack (Variation.eta a b c) first
  have naturalSecond := argumentTrack (Variation.eta a b c) second
  simp only [Variation.right, holeTrack] at naturalFirst naturalSecond
  have square : Cell (.comp (.step (.root (.eta p))) first) (.comp (.step (.root (.eta p))) second) :=
    naturalFirst.symm.trans
      ((Four.comp observed (.refl _)).trans naturalSecond)
  exact FourNaturality.cancelPrefix (.step (.root (.eta p))) square

theorem comparable_iff_projections {a b c : Shape Atom} {p q : Wire a (.pair b c)}
    (first second : ProofTrack p q) : Nonempty (Cell first second) ↔
      Nonempty (Cell (firstProjection first) (firstProjection second)) ∧
      Nonempty (Cell (secondProjection first) (secondProjection second)) :=
  ⟨fun ⟨cell⟩ => ⟨⟨cell.whisker (.seqLeft (fst b c))⟩, ⟨cell.whisker (.seqLeft (snd b c))⟩⟩,
    fun ⟨⟨left⟩, ⟨right⟩⟩ => ⟨reflect first second left right⟩⟩

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian.Higher.ProductTracks
