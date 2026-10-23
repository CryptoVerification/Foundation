import Foundation.Logic.Polygraph.Higher

/-! Groupoid square pasting and extension of single-step naturality to actual
tracks. All operations are derived Four cells; no whole-track naturality
constructor or arbitrary parallel-track generator is introduced. -/
namespace Foundation.Logic.Polygraph.FourNaturality

variable {A B C : Type*} {R : A → A → Type*} {S : B → B → Type*} {T : C → C → Type*}

theorem map_map (f : A → B) (g : B → C)
    (first : ∀ {a b}, R a b → S (f a) (f b)) (second : ∀ {a b}, S a b → T (g a) (g b))
    {a b} (path : Track R a b) :
    (path.map f first).map g second = path.map (fun x => g (f x)) (fun step => second (first step)) := by
  induction path <;> simp_all only [Track.map]

variable {Cells : {a b : B} → Track S a b → Track S a b → Type*}

def undoRight {a b c : B} (p : Track S a b) (q : Track S b c) :
    Four Cells (.comp (.comp p q) (.inv q)) p :=
  (Four.assoc p q (.inv q)).trans ((Four.comp (.refl p) (.rightInv q)).trans (.rightUnit p))

def undoLeft {a b c : B} (p : Track S a b) (q : Track S a c) :
    Four Cells (.comp p (.comp (.inv p) q)) q :=
  (Four.assoc p (.inv p) q).symm.trans ((Four.comp (.rightInv p) (.refl q)).trans (.leftUnit q))

def undoInversePrefix {a b c : B} (p : Track S a b) (q : Track S b c) :
    Four Cells (.comp (.inv p) (.comp p q)) q :=
  (Four.assoc (.inv p) p q).symm.trans ((Four.comp (.leftInv p) (.refl q)).trans (.leftUnit q))

def cancelPrefix {a b c : B} (r : Track S a b) {p q : Track S b c}
    (cell : Four Cells (.comp r p) (.comp r q)) : Four Cells p q :=
  (undoInversePrefix r p).symm.trans ((Four.comp (.refl (.inv r)) cell).trans (undoInversePrefix r q))

def invertSquare {a b c d : B} (p : Track S a b) (s : Track S b d)
    (r : Track S a c) (q : Track S c d) (cell : Four Cells (.comp p s) (.comp r q)) :
    Four Cells (.comp (.inv p) r) (.comp s (.inv q)) :=
  cancelPrefix p ((undoLeft p r).trans
    (((Four.assoc p s (.inv q)).symm.trans
      ((Four.comp cell (.refl (.inv q))).trans (undoRight r q))).symm))

def natural (f g : A → B) (mapF : ∀ {a b}, R a b → S (f a) (f b))
    (mapG : ∀ {a b}, R a b → S (g a) (g b)) (component : ∀ a, Track S (f a) (g a))
    (stepSquare : ∀ {a b} (step : R a b),
      Four Cells (.comp (.step (mapF step)) (component b)) (.comp (component a) (.step (mapG step)))) :
    {a b : A} → (path : Track R a b) →
      Four Cells (.comp (path.map f mapF) (component b)) (.comp (component a) (path.map g mapG))
  | a, _, .refl _ => (Four.leftUnit (component a)).trans (Four.rightUnit (component a)).symm
  | _, _, .step step => stepSquare step
  | a, c, .comp (b := b) first second =>
      (Four.assoc (first.map f mapF) (second.map f mapF) (component c)).trans
        ((Four.comp (.refl (first.map f mapF)) (natural f g mapF mapG component stepSquare second)).trans
          ((Four.assoc (first.map f mapF) (component b) (second.map g mapG)).symm.trans
            ((Four.comp (natural f g mapF mapG component stepSquare first) (.refl (second.map g mapG))).trans
              (Four.assoc (component a) (first.map g mapG) (second.map g mapG)))))
  | a, b, .inv child =>
      invertSquare (child.map f mapF) (component a) (component b) (child.map g mapG)
        (natural f g mapF mapG component stepSquare child)

end Foundation.Logic.Polygraph.FourNaturality
