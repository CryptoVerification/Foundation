import Foundation.Logic.Polygraph.FiniteConfluence

/-! Full coherence for reversible typed composition paths, derived from the
finite schematic basis. Components merely fix the common terminal expression;
all comparisons are returned as Finite.Cell4 data on the original raw paths.
No normalizing-square generator is used. -/
namespace Foundation.Logic.Polygraph.Composition.Finite

universe u v
variable {O : Type u} {E : O → O → Type v}
open Expr

variable {a b : O}

abbrev Vertex (k : Chain E a b) := {f : Expr E a b // f.flatten = k}
abbrev Edge (k : Chain E a b) (f g : Vertex k) := Step f.val g.val

def normalPath (k : Chain E a b) (f : Vertex k) : Path f.val k.reflect :=
  (congrArg Chain.reflect f.property) ▸ normalizePath f.val

def normal3 (k : Chain E a b) (f : Vertex k) : Three f.val k.reflect :=
  Track.ofPath (normalPath k f)

def forget {k : Chain E a b} {f g : Vertex k} (p : Track (Edge k) f g) : Three f.val g.val :=
  p.map (S := fun x y => Step x y) Subtype.val (fun s => s)

/-- The single-step contraction is now a theorem constructed from the local
finite basis, not an additional four-dimensional generator. -/
def contract {k : Chain E a b} : {f g : Vertex k} → (p : Track (Edge k) f g) →
    Cell4 (.comp (forget p) (normal3 k g)) (normal3 k f)
  | _, _, .refl _ => .leftUnit _
  | _, _, .step s => terminalCoherence (fun s => reflect_irreducible k s)
      (.cons s (normalPath k _)) (normalPath k _)
  | _, _, .comp p q =>
      (Cell4.assoc (forget p) (forget q) _).trans
        ((Cell4.comp (.refl (forget p)) (contract q)).trans (contract p))
  | _, _, .inv p =>
      (Cell4.comp (.refl (.inv (forget p))) (contract p).symm).trans
        ((Cell4.assoc (.inv (forget p)) (forget p) _).symm.trans
          ((Cell4.comp (.leftInv (forget p)) (.refl _)).trans (.leftUnit _)))

def factor {k : Chain E a b} {f g : Vertex k} (p : Track (Edge k) f g) :
    Cell4 (forget p) (.comp (normal3 k f) (.inv (normal3 k g))) :=
  (Cell4.rightUnit (forget p)).symm.trans
    ((Cell4.comp (.refl (forget p)) (Cell4.rightInv (normal3 k g)).symm).trans
      ((Cell4.assoc (forget p) (normal3 k g) (.inv (normal3 k g))).symm.trans
        (Cell4.comp (contract p) (.refl _))))

def coherentComponent {k : Chain E a b} {f g : Vertex k}
    (p q : Track (Edge k) f g) : Cell4 (forget p) (forget q) :=
  (factor p).trans (factor q).symm

theorem track_key {f g : Expr E a b} (p : Three f g) : f.flatten = g.flatten := by
  induction p with
  | refl => rfl
  | step s => exact s.flatten_eq
  | comp p q ihp ihq => exact ihp.trans ihq
  | inv p ih => exact ih.symm

def liftTrack {k : Chain E a b} : {f g : Expr E a b} → (p : Three f g) →
    (hf : f.flatten = k) → Track (Edge k) ⟨f, hf⟩ ⟨g, (track_key p).symm.trans hf⟩
  | _, _, .refl _, _ => .refl _
  | _, _, .step s, _ => .step s
  | _, _, .comp p q, hf => .comp (liftTrack p hf) (liftTrack q ((track_key p).symm.trans hf))
  | _, _, .inv p, hf => .inv (liftTrack p ((track_key p).trans hf))

theorem forget_liftTrack {k : Chain E a b} {f g : Expr E a b}
    (p : Three f g) (hf : f.flatten = k) : forget (liftTrack p hf) = p := by
  induction p with
  | refl => rfl
  | step => rfl
  | comp p q ihp ihq =>
      change Track.comp (forget (liftTrack p hf))
        (forget (liftTrack q ((track_key p).symm.trans hf))) = .comp p q
      rw [ihp, ihq]
  | inv p ih =>
      change Track.inv (forget (liftTrack p ((track_key p).trans hf))) = .inv p
      rw [ih]

/-- Finite schematic coherence: every parallel pair of association/unit
tracks is joined by a four-cell using only the eleven basic diagram forms. -/
def coherent {f g : Expr E a b} (p q : Three f g) : Cell4 p q := by
  have comparison := coherentComponent (liftTrack p (k := f.flatten) rfl) (liftTrack q rfl)
  simpa only [forget_liftTrack] using comparison

end Foundation.Logic.Polygraph.Composition.Finite
