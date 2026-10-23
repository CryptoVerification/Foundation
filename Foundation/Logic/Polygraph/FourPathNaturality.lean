import Foundation.Logic.Polygraph.FourNaturality

/-! Substitution of finite proof tracks for edges, and higher naturality for
path-valued edge maps. Zero-step and multi-step images are ordinary data; no
whole-path higher generator or inverse execution operation is introduced. -/
namespace Foundation.Logic.Polygraph.FourPathNaturality
variable {A B : Type*} {R : A → A → Type*} {S : B → B → Type*}

def replace (f : A → B) (edge : ∀ {a b}, R a b → Track S (f a) (f b)) :
    {a b : A} → Track R a b → Track S (f a) (f b)
  | a, _, .refl _ => .refl (f a)
  | _, _, .step change => edge change
  | _, _, .comp first second => .comp (replace f edge first) (replace f edge second)
  | _, _, .inv child => .inv (replace f edge child)

theorem replace_single (f : A → B) (edge : ∀ {a b}, R a b → S (f a) (f b))
    {a b} (path : Track R a b) : replace f (fun change => .step (edge change)) path = path.map f edge := by
  induction path <;> simp_all only [replace, Track.map]

variable {Cells : {a b : B} → Track S a b → Track S a b → Type*}

def natural (f g : A → B) (mapF : ∀ {a b}, R a b → Track S (f a) (f b))
    (mapG : ∀ {a b}, R a b → Track S (g a) (g b)) (component : ∀ a, Track S (f a) (g a))
    (stepSquare : ∀ {a b} (step : R a b),
      Four Cells (.comp (mapF step) (component b)) (.comp (component a) (mapG step))) :
    {a b : A} → (path : Track R a b) →
      Four Cells (.comp (replace f mapF path) (component b)) (.comp (component a) (replace g mapG path))
  | a, _, .refl _ => (Four.leftUnit (component a)).trans (Four.rightUnit (component a)).symm
  | _, _, .step step => stepSquare step
  | a, c, .comp (b := b) first second =>
      (Four.assoc (replace f mapF first) (replace f mapF second) (component c)).trans
        ((Four.comp (.refl (replace f mapF first)) (natural f g mapF mapG component stepSquare second)).trans
          ((Four.assoc (replace f mapF first) (component b) (replace g mapG second)).symm.trans
            ((Four.comp (natural f g mapF mapG component stepSquare first) (.refl (replace g mapG second))).trans
              (Four.assoc (component a) (replace g mapG first) (replace g mapG second)))))
  | a, b, .inv child =>
      FourNaturality.invertSquare (replace f mapF child) (component a) (component b) (replace g mapG child)
        (natural f g mapF mapG component stepSquare child)

end Foundation.Logic.Polygraph.FourPathNaturality
