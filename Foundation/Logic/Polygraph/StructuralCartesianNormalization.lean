import Foundation.Logic.Polygraph.StructuralCartesianPresentation

/-! Constructive first-level normalization using the eighteen displayed roots.
Normalization is a recursive derived proof, never a root generator. Higher
coherence between these proofs is a separate obligation. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Cartesian
open TypedRouting
variable {Atom : Type}
set_option backward.isDefEq.respectTransparency false

def reifyRef : {a : Shape Atom} → {name : Atom} → Slot a name → Wire a (.atom name)
  | _, _, .here name => .identity (.atom name)
  | _, _, .left slot => .seq (fst _ _) (reifyRef slot)
  | _, _, .right slot => .seq (snd _ _) (reifyRef slot)

def reify {a : Shape Atom} : {b : Shape Atom} → Layout a b → Wire a b
  | .atom _, slot => reifyRef slot
  | .unit, _ => .discard a
  | .pair _ _, layout => fork (reify layout.1) (reify layout.2)

theorem reifyRef_correct {family : Atom → Type} {a : Shape Atom} {name} (slot : Slot a name) (value : a.Value family) :
    (reifyRef slot).eval family value = read slot value := by
  induction slot with
  | here => rfl
  | left slot ih => exact ih value.1
  | right slot ih => exact ih value.2

theorem reify_correct {family : Atom → Type} {a b : Shape Atom} (layout : Layout a b) (value : a.Value family) :
    (reify layout).eval family value = b.map (fun _ slot => read slot value) layout := by
  induction b with
  | atom => exact reifyRef_correct layout value
  | unit => rfl
  | pair b c one two => exact congrArg₂ Prod.mk (one layout.1) (two layout.2)

theorem reify_normal {a b : Shape Atom} (layout : Layout a b) : normal (reify layout) = layout := by
  rw [normal, reify_correct]
  simp only [read_universal, map_identity]

def liftLeft {a b : Shape Atom} : {c : Shape Atom} → (layout : Layout a c) →
    Cell (.seq (fst a b) (reify layout)) (reify (c.map (fun _ => Slot.left) layout))
  | .atom _, _ => .refl _
  | .unit, _ => .root (.discardAfter _)
  | .pair _ _, layout =>
      (Cell.root (.forkAfter _ _ _)).trans (.fork (liftLeft layout.1) (liftLeft layout.2))

def liftRight {a b : Shape Atom} : {c : Shape Atom} → (layout : Layout b c) →
    Cell (.seq (snd a b) (reify layout)) (reify (c.map (fun _ => Slot.right) layout))
  | .atom _, _ => .refl _
  | .unit, _ => .root (.discardAfter _)
  | .pair _ _, layout =>
      (Cell.root (.forkAfter _ _ _)).trans (.fork (liftRight layout.1) (liftRight layout.2))

def projectLeft (a b : Shape Atom) (normalized : Cell (.identity a) (reify (universal a))) :
    Cell (fst a b) (reify (a.map (fun _ => Slot.left) (universal a))) :=
  (Cell.root (.rightId _)).symm.trans ((Cell.seq (.refl _) normalized).trans (liftLeft _))

def projectRight (a b : Shape Atom) (normalized : Cell (.identity b) (reify (universal b))) :
    Cell (snd a b) (reify (b.map (fun _ => Slot.right) (universal b))) :=
  (Cell.root (.rightId _)).symm.trans ((Cell.seq (.refl _) normalized).trans (liftRight _))

def identityNormal : (a : Shape Atom) → Cell (.identity a) (reify (universal a))
  | .atom _ => .refl _
  | .unit => .root .unitIdentity
  | .pair a b =>
      (Cell.root (.eta (.identity (.pair a b)))).symm.trans
        (.fork ((Cell.root (.leftId _)).trans (projectLeft a b (identityNormal a)))
          ((Cell.root (.leftId _)).trans (projectRight a b (identityNormal b))))

def selectNormal {a : Shape Atom} : {b : Shape Atom} → (layout : Layout a b) → {name : Atom} → (slot : Slot b name) →
    Cell (.seq (reify layout) (reifyRef slot)) (reifyRef (read slot layout))
  | _, _, _, .here _ => .root (.rightId _)
  | _, layout, _, .left slot =>
      (Cell.root (.assoc _ _ _)).symm.trans
        ((Cell.seq (Cell.root (.betaFst _ _)) (.refl _)).trans (selectNormal layout.1 slot))
  | _, layout, _, .right slot =>
      (Cell.root (.assoc _ _ _)).symm.trans
        ((Cell.seq (Cell.root (.betaSnd _ _)) (.refl _)).trans (selectNormal layout.2 slot))

def substitute {a b c : Shape Atom} (first : Layout a b) (second : Layout b c) : Layout a c :=
  c.map (fun _ slot => read slot first) second

def seqNormal {a b : Shape Atom} (first : Layout a b) : {c : Shape Atom} → (second : Layout b c) →
    Cell (.seq (reify first) (reify second)) (reify (substitute first second))
  | .atom _, slot => selectNormal first slot
  | .unit, _ => .root (.discardAfter _)
  | .pair _ _, layout =>
      (Cell.root (.forkAfter _ _ _)).trans (.fork (seqNormal first layout.1) (seqNormal first layout.2))

structure Normalized {a b : Shape Atom} (wire : Wire a b) where
  layout : Layout a b
  certificate : Cell wire (reify layout)

namespace Normalized

def before {a b : Shape Atom} {p q : Wire a b} (change : Cell p q) (normalized : Normalized q) : Normalized p :=
  ⟨normalized.layout, change.trans normalized.certificate⟩

def identity (a : Shape Atom) : Normalized (.identity a) := ⟨universal a, identityNormal a⟩
def terminal (a : Shape Atom) : Normalized (.discard a) := ⟨PUnit.unit, .refl _⟩
def leftProjection (a b : Shape Atom) : Normalized (fst a b) :=
  ⟨a.map (fun _ => Slot.left) (universal a), projectLeft a b (identityNormal a)⟩
def rightProjection (a b : Shape Atom) : Normalized (snd a b) :=
  ⟨b.map (fun _ => Slot.right) (universal b), projectRight a b (identityNormal b)⟩

def seq {a b c : Shape Atom} {p : Wire a b} {q : Wire b c} (first : Normalized p) (second : Normalized q) : Normalized (.seq p q) :=
  ⟨substitute first.layout second.layout, (Cell.seq first.certificate second.certificate).trans (seqNormal _ _)⟩

def pair {a b c : Shape Atom} {p : Wire a b} {q : Wire a c} (first : Normalized p) (second : Normalized q) : Normalized (fork p q) :=
  ⟨(first.layout, second.layout), .fork first.certificate second.certificate⟩

end Normalized

def normalize : {a b : Shape Atom} → (wire : Wire a b) → Normalized wire
  | _, _, .identity a => .identity a
  | _, _, .seq p q => .seq (normalize p) (normalize q)
  | _, _, .tensor (first := a) (first' := c) p q =>
      .before (Cell.root (.tensorExpand p q)) (.pair (.seq (.leftProjection a c) (normalize p)) (.seq (.rightProjection a c) (normalize q)))
  | _, _, .copy a => .before (Cell.root (.copyExpand a)) (.pair (.identity a) (.identity a))
  | _, _, .discard a => .terminal a
  | _, _, .swap a b => .before (Cell.root (.swapExpand a b)) (.pair (.rightProjection a b) (.leftProjection a b))
  | _, _, .assoc a b c => .before (Cell.root (.assocExpand a b c))
      (.pair (.seq (.leftProjection (.pair a b) c) (.leftProjection a b))
        (.pair (.seq (.leftProjection (.pair a b) c) (.rightProjection a b)) (.rightProjection (.pair a b) c)))
  | _, _, .unassoc a b c => .before (Cell.root (.unassocExpand a b c))
      (.pair (.pair (.leftProjection a (.pair b c)) (.seq (.rightProjection a (.pair b c)) (.leftProjection b c)))
        (.seq (.rightProjection a (.pair b c)) (.rightProjection b c)))
  | _, _, .leftUnit a => .before (Cell.root (.leftUnitExpand a)) (.rightProjection .unit a)
  | _, _, .rightUnit a => .before (Cell.root (.rightUnitExpand a)) (.leftProjection a .unit)
  | _, _, .leftUnitInv a => .before (Cell.root (.leftUnitInvExpand a)) (.pair (.terminal a) (.identity a))
  | _, _, .rightUnitInv a => .before (Cell.root (.rightUnitInvExpand a)) (.pair (.identity a) (.terminal a))

theorem normalize_layout {a b : Shape Atom} (wire : Wire a b) : (normalize wire).layout = normal wire := by
  have same := (normalize wire).certificate.sound (Slot a) (universal a)
  change normal wire = normal (reify (normalize wire).layout) at same
  rw [reify_normal] at same
  exact same.symm

def normalizeCell {a b : Shape Atom} (wire : Wire a b) : Cell wire (reify (normal wire)) :=
  (normalize_layout wire) ▸ (normalize wire).certificate

theorem canonical_idempotent {a b : Shape Atom} (wire : Wire a b) :
    reify (normal (reify (normal wire))) = reify (normal wire) := by
  rw [reify_normal]

def connect {a b : Shape Atom} (first second : Wire a b) (same : normal first = normal second) : Cell first second :=
  (normalizeCell first).trans (same ▸ (normalizeCell second).symm)

theorem complete {a b : Shape Atom} (first second : Wire a b) :
    Nonempty (Cell first second) ↔ ∀ (family : Atom → Type) (value : a.Value family), first.eval family value = second.eval family value := by
  constructor
  · rintro ⟨cell⟩ family value
    exact cell.sound family value
  · intro same
    exact ⟨connect first second ((normal_complete first second).mpr same)⟩

end Foundation.Logic.Polygraph.StructuralTransport.Cartesian
