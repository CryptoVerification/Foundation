import Foundation.Logic.Polygraph.CriticalBranchings

/-! Homotopical confluence from the finite local basis. Induction decreases
the weight of the source expression. Normalization is used to choose a common
terminal suffix, but no normalization comparison is assumed as a generator. -/
namespace Foundation.Logic.Polygraph.Composition.Finite

universe u v
variable {O : Type u} {E : O → O → Type v}
open Expr

theorem terminal_path {a b : O} {n f : Expr E a b}
    (hn : ∀ {g}, Step n g → False) (p : Path n f) : n = f := by
  cases p with
  | refl => rfl
  | cons s _ => exact False.elim (hn s)

theorem terminal_normal {a b : O} {n : Expr E a b}
    (hn : ∀ {g}, Step n g → False) : n.normal = n :=
  (terminal_path hn (normalizePath n)).symm

def toTerminal {a b : O} {z n : Expr E a b} (hn : ∀ {g}, Step n g → False)
    (h : z.flatten = n.flatten) : Path z n :=
  ((congrArg Chain.reflect h).trans (terminal_normal hn)) ▸ normalizePath z

def continueRoute {a b : O} {f g h i : Expr E a b} (s : Step f g)
    (p : Path g h) (q : Path h i) :
    Cell4 (route s (p.comp q)) (.comp (route s p) (Track.ofPath q)) :=
  (Cell4.comp (.refl (.step s)) (Cell4.pathComp p q)).trans
    (Cell4.assoc (.step s) _ _).symm

/-- Every two directed paths to the same irreducible endpoint are compared
using only the finite local generators, context closure, and groupoid laws. -/
def terminalCoherence {a b : O} : {f n : Expr E a b} →
    (hn : ∀ {g}, Step n g → False) → (p q : Path f n) →
    Cell4 (Track.ofPath p) (Track.ofPath q)
  | _, _, _, .refl _, .refl _ => .refl _
  | _, _, hn, .refl _, .cons s _ => False.elim (hn s)
  | _, _, hn, .cons s _, .refl _ => False.elim (hn s)
  | _, _, hn, .cons s p, .cons t q =>
      let j := localJoin s t
      let tail := toTerminal hn ((Expr.Path.flatten_eq j.first).symm.trans (Expr.Path.flatten_eq p))
      let ip := terminalCoherence hn p (j.first.comp tail)
      let iq := terminalCoherence hn q (j.second.comp tail)
      (Cell4.comp (.refl (.step s)) ip).trans
        ((continueRoute s j.first tail).trans
          ((Cell4.comp j.square (.refl (Track.ofPath tail))).trans
            ((continueRoute t j.second tail).symm.trans
              (Cell4.comp (.refl (.step t)) iq).symm)))
  termination_by f _ _ _ _ => f.weight
  decreasing_by
    · exact s.decreases.1
    · exact t.decreases.1

/-- The previously supplied normalizing square is derivable from the local
finite basis for every step. It is no longer needed as a primitive generator. -/
def stepNormalization {a b : O} {f g : Expr E a b} (s : Step f g) :
    Cell4
      (route s (toTerminal (fun step => normal_irreducible f step)
        (s.flatten_eq.symm.trans (flatten_reflect f.flatten).symm)))
      (Track.ofPath (normalizePath f)) :=
  terminalCoherence (fun step => normal_irreducible f step)
    (.cons s (toTerminal (fun step => normal_irreducible f step)
      (s.flatten_eq.symm.trans (flatten_reflect f.flatten).symm))) (normalizePath f)

end Foundation.Logic.Polygraph.Composition.Finite
