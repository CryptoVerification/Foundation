import Foundation.Logic.Polygraph.Normalization
import Foundation.Logic.Polygraph.Higher

/-! A finite schematic homotopy basis for typed association and unit rewriting.
The basis contains five critical diagrams, five variable-overlap naturality
diagrams, and disjoint exchange. It contains no normalization-square schema.
Contexts and groupoid pasting are structural operations, not extra critical
diagrams. Finiteness refers to rule forms, not their typed instances. -/
namespace Foundation.Logic.Polygraph.Composition.Finite

universe u v
variable {O : Type u} {E : O → O → Type v}
open Expr

abbrev Three {a b : O} (f g : Expr E a b) := Track (@Step O E a b) f g

def left {a b c : O} {f f' : Expr E a b} (p : Three f f') (g : Expr E b c) :
    Three (.seq f g) (.seq f' g) :=
  p.map (S := fun x y => Step x y) (fun f => Expr.seq f g) (fun s => Step.left s g)

def right {a b c : O} (f : Expr E a b) {g g' : Expr E b c} (p : Three g g') :
    Three (.seq f g) (.seq f g') :=
  p.map (S := fun x y => Step x y) (fun g => Expr.seq f g) (fun s => Step.right f s)

abbrev route {a b : O} {f g h : Expr E a b} (s : Step f g) (p : Path g h) : Three f h :=
  .comp (.step s) (Track.ofPath p)

inductive Generator : {a b : O} → {f g : Expr E a b} → Three f g → Three f g →
    Type (max u v) where
  | pentagon {a b c d e} (f : Expr E a b) (g : Expr E b c)
      (h : Expr E c d) (i : Expr E d e) :
      Generator
        (route (.assoc (.seq f g) h i) (.single (.assoc f g (.seq h i))))
        (route (.left (.assoc f g h) i)
          (.cons (.assoc f (.seq g h) i) (.single (.right f (.assoc g h i)))))
  | assocLeftUnit {a b c} (f : Expr E a b) (g : Expr E b c) :
      Generator (route (.assoc (.identity a) f g) (.single (.leftUnit (.seq f g))))
        (route (.left (.leftUnit f) g) (.refl _))
  | assocMiddleUnit {a b c} (f : Expr E a b) (g : Expr E b c) :
      Generator (route (.assoc f (.identity b) g) (.single (.right f (.leftUnit g))))
        (route (.left (.rightUnit f) g) (.refl _))
  | assocRightUnit {a b c} (f : Expr E a b) (g : Expr E b c) :
      Generator (route (.assoc f g (.identity c)) (.single (.right f (.rightUnit g))))
        (route (.rightUnit (.seq f g)) (.refl _))
  | units (a : O) : Generator
      (route (.leftUnit (.identity (E := E) a)) (.refl _))
      (route (.rightUnit (.identity (E := E) a)) (.refl _))
  | leftUnitNatural {a b} {f f' : Expr E a b} (s : Step f f') :
      Generator (route (.leftUnit f) (.single s))
        (route (.right (.identity a) s) (.single (.leftUnit f')))
  | rightUnitNatural {a b} {f f' : Expr E a b} (s : Step f f') :
      Generator (route (.rightUnit f) (.single s))
        (route (.left s (.identity b)) (.single (.rightUnit f')))
  | assocNaturalFirst {a b c d} {f f' : Expr E a b} (s : Step f f')
      (g : Expr E b c) (h : Expr E c d) :
      Generator (route (.assoc f g h) (.single (.left s (.seq g h))))
        (route (.left (.left s g) h) (.single (.assoc f' g h)))
  | assocNaturalSecond {a b c d} (f : Expr E a b) {g g' : Expr E b c} (s : Step g g')
      (h : Expr E c d) :
      Generator (route (.assoc f g h) (.single (.right f (.left s h))))
        (route (.left (.right f s) h) (.single (.assoc f g' h)))
  | assocNaturalThird {a b c d} (f : Expr E a b) (g : Expr E b c)
      {h h' : Expr E c d} (s : Step h h') :
      Generator (route (.assoc f g h) (.single (.right f (.right g s))))
        (route (.right (.seq f g) s) (.single (.assoc f g h')))
  | exchange {a b c} {f f' : Expr E a b} {g g' : Expr E b c}
      (s : Step f f') (t : Step g g') :
      Generator (route (.left s g) (.single (.right f' t)))
        (route (.right f t) (.single (.left s g')))

/-- The finite presentation is freely closed under groupoid pasting and
under left/right expression contexts. -/
inductive Cell4 : {a b : O} → {f g : Expr E a b} → Three f g → Three f g →
    Type (max u v) where
  | generator {a b} {f g : Expr E a b} {p q : Three f g} : Generator p q → Cell4 p q
  | law {a b} {f g : Expr E a b} {p q : Three f g} :
      Four (fun {_ _} _ _ => PEmpty.{1}) p q → Cell4 p q
  | symm {a b} {f g : Expr E a b} {p q : Three f g} : Cell4 p q → Cell4 q p
  | trans {a b} {f g : Expr E a b} {p q r : Three f g} : Cell4 p q → Cell4 q r → Cell4 p r
  | comp {a b} {f g h : Expr E a b} {p p' : Three f g} {q q' : Three g h} :
      Cell4 p p' → Cell4 q q' → Cell4 (.comp p q) (.comp p' q')
  | inverse {a b} {f g : Expr E a b} {p q : Three f g} : Cell4 p q → Cell4 (.inv p) (.inv q)
  | left {a b c} {f f' : Expr E a b} {p q : Three f f'} (s : Cell4 p q) (g : Expr E b c) :
      Cell4 (Finite.left p g) (Finite.left q g)
  | right {a b c} (f : Expr E a b) {g g' : Expr E b c} {p q : Three g g'} (s : Cell4 p q) :
      Cell4 (Finite.right f p) (Finite.right f q)

namespace Cell4
variable {a b : O} {f g h i : Expr E a b}

def refl (p : Three f g) : Cell4 p p := .law (.refl p)
def assoc (p : Three f g) (q : Three g h) (r : Three h i) :
    Cell4 (.comp (.comp p q) r) (.comp p (.comp q r)) := .law (.assoc p q r)
def leftUnit (p : Three f g) : Cell4 (.comp (.refl f) p) p := .law (.leftUnit p)
def rightUnit (p : Three f g) : Cell4 (.comp p (.refl g)) p := .law (.rightUnit p)
def leftInv (p : Three f g) : Cell4 (.comp (.inv p) p) (.refl g) := .law (.leftInv p)
def rightInv (p : Three f g) : Cell4 (.comp p (.inv p)) (.refl f) := .law (.rightInv p)

def pathComp : {f g h : Expr E a b} → (p : Path f g) → (q : Path g h) →
    Cell4 (Track.ofPath (p.comp q)) (.comp (Track.ofPath p) (Track.ofPath q))
  | _, _, _, .refl _, _ => (leftUnit _).symm
  | _, _, _, .cons s p, q =>
      (Cell4.comp (refl (.step s)) (pathComp p q)).trans (assoc (.step s) _ _).symm

end Cell4

theorem ofPath_left {a b c : O} {f f' : Expr E a b} (p : Path f f') (g : Expr E b c) :
    Track.ofPath (Expr.Path.left p g) = left (Track.ofPath p) g := by
  induction p with
  | refl => rfl
  | cons s p ih => exact congrArg (Track.comp (.step (.left s g))) ih

theorem ofPath_right {a b c : O} (f : Expr E a b) {g g' : Expr E b c} (p : Path g g') :
    Track.ofPath (Expr.Path.right f p) = right f (Track.ofPath p) := by
  induction p with
  | refl => rfl
  | cons s p ih => exact congrArg (Track.comp (.step (.right f s))) ih

inductive ForkKind where
  | identical | pentagon | assocLeftUnit | assocMiddleUnit | assocRightUnit | units
  | leftUnitNatural | rightUnitNatural | assocNaturalFirst | assocNaturalSecond | assocNaturalThird
  | exchange | nestedLeft | nestedRight
  deriving DecidableEq, Repr

structure Join {a b : O} {f g h : Expr E a b} (s : Step f g) (t : Step f h) where
  target : Expr E a b
  first : Path g target
  second : Path h target
  square : Cell4 (route s first) (route t second)
  kind : ForkKind

namespace Join
variable {a b : O} {f g h : Expr E a b} {s : Step f g} {t : Step f h}

def same (s : Step f g) : Join s s := ⟨g, .refl _, .refl _, .refl _, .identical⟩
def swap (j : Join s t) : Join t s := ⟨j.target, j.second, j.first, j.square.symm, j.kind⟩

def left {c : O} (j : Join s t) (i : Expr E b c) : Join (.left s i) (.left t i) :=
  ⟨.seq j.target i, j.first.left i, j.second.left i, by
    simpa only [route, ofPath_left, Finite.left, Track.map] using Cell4.left j.square i, .nestedLeft⟩

def right {c : O} (i : Expr E c a) (j : Join s t) : Join (.right i s) (.right i t) :=
  ⟨.seq i j.target, Expr.Path.right i j.first, Expr.Path.right i j.second, by
    simpa only [route, ofPath_right, Finite.right, Track.map] using Cell4.right i j.square, .nestedRight⟩

end Join

end Foundation.Logic.Polygraph.Composition.Finite
