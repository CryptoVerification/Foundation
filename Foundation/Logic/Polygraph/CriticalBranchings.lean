import Foundation.Logic.Polygraph.FiniteCoherence

/-! Exhaustive typed classification of forks of association/unit rewrites.
Root overlaps use the five critical diagrams. Variable overlaps use the five
naturality forms; disjoint positions use exchange. Overlaps inside the same
context are classified recursively. No confluence oracle is used here. -/
namespace Foundation.Logic.Polygraph.Composition.Finite

universe u v
variable {O : Type u} {E : O → O → Type v}
open Expr

def leftUnitJoin {a b : O} (f : Expr E a b) {h : Expr E a b}
    (t : Step (.seq (.identity a) f) h) : Join (.leftUnit f) t := by
  cases t with
  | leftUnit => exact Join.same _
  | rightUnit => exact ⟨_, .refl _, .refl _, .generator (.units _), .units⟩
  | left s _ => cases s
  | right _ s => exact ⟨_, .single s, .single (.leftUnit _),
      .generator (.leftUnitNatural s), .leftUnitNatural⟩

def rightUnitJoin {a b : O} (f : Expr E a b) {h : Expr E a b}
    (t : Step (.seq f (.identity b)) h) : Join (.rightUnit f) t := by
  cases t with
  | assoc f g _ => exact Join.swap ⟨_, .single (.right f (.rightUnit g)), .refl _,
      .generator (.assocRightUnit f g), .assocRightUnit⟩
  | leftUnit => exact Join.swap ⟨_, .refl _, .refl _, .generator (.units _), .units⟩
  | rightUnit => exact Join.same _
  | left s _ => exact ⟨_, .single s, .single (.rightUnit _),
      .generator (.rightUnitNatural s), .rightUnitNatural⟩
  | right _ s => cases s

def assocJoin {a b c d : O} (f : Expr E a b) (g : Expr E b c) (h : Expr E c d)
    {k : Expr E a d} (t : Step (.seq (.seq f g) h) k) : Join (.assoc f g h) t := by
  cases t with
  | assoc => exact Join.same _
  | rightUnit => exact ⟨_, .single (.right f (.rightUnit g)), .refl _,
      .generator (.assocRightUnit f g), .assocRightUnit⟩
  | left s _ =>
      cases s with
      | assoc f g => exact ⟨_, .single (.assoc f g (.seq _ h)),
          .cons (.assoc f (.seq g _) h) (.single (.right f (.assoc g _ h))),
          .generator (.pentagon f g _ h), .pentagon⟩
      | leftUnit => exact ⟨_, .single (.leftUnit (.seq _ h)), .refl _,
          .generator (.assocLeftUnit _ h), .assocLeftUnit⟩
      | rightUnit f => exact ⟨_, .single (.right f (.leftUnit h)), .refl _,
          .generator (.assocMiddleUnit f h), .assocMiddleUnit⟩
      | left s g => exact ⟨_, .single (.left s (.seq g h)), .single (.assoc _ g h),
          .generator (.assocNaturalFirst s g h), .assocNaturalFirst⟩
      | right f s => exact ⟨_, .single (.right f (.left s h)), .single (.assoc f _ h),
          .generator (.assocNaturalSecond f s h), .assocNaturalSecond⟩
  | right _ s => exact ⟨_, .single (.right f (.right g s)), .single (.assoc f g _),
      .generator (.assocNaturalThird f g s), .assocNaturalThird⟩

/-- Every ordered pair of coinitial rewrites receives a classified, directed
joining diagram and a four-cell from the finite schematic basis. -/
def localJoin : {a b : O} → {f g h : Expr E a b} → (s : Step f g) → (t : Step f h) → Join s t
  | _, _, _, _, _, .assoc f g h, t => assocJoin f g h t
  | _, _, _, _, _, .leftUnit f, t => leftUnitJoin f t
  | _, _, _, _, _, .rightUnit f, t => rightUnitJoin f t
  | _, _, _, _, _, .left s g, t => by
      cases t with
      | assoc f h g => exact (assocJoin f h g (.left s g)).swap
      | leftUnit => cases s
      | rightUnit => exact (rightUnitJoin _ (.left s _)).swap
      | left t g => exact (localJoin s t).left g
      | right f t => exact ⟨_, .single (.right _ t), .single (.left s _),
          .generator (.exchange s t), .exchange⟩
  | _, _, _, _, _, .right f s, t => by
      cases t with
      | assoc f g => exact (assocJoin f g _ (.right (.seq f g) s)).swap
      | leftUnit => exact (leftUnitJoin _ (.right _ s)).swap
      | rightUnit => cases s
      | left t g => exact (Join.mk _ (.single (.right _ s)) (.single (.left t _))
          (Cell4.generator (.exchange t s)) .exchange).swap
      | right f t => exact (localJoin s t).right f
  termination_by _ _ _ _ _ s _ => sizeOf s
  decreasing_by all_goals (simp_wf; omega)

end Foundation.Logic.Polygraph.Composition.Finite
