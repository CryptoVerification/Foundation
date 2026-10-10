import Foundation.Quantum.SpectralGenerators

/-! A finite calculus for Heunen 5.2.10 (body pp.152–153). The regular-cover
term denotes a specified countable join; it is not an infinitary derivation
constructor. This syntax and its finite order rules are our reconstruction.
There is no rule admitting an arbitrary true semantic inequality. -/
namespace Foundation.Quantum.Bohr.GeneratorLogic
noncomputable section
open Foundation.Logic
set_option backward.isDefEq.respectTransparency false
variable {A : Type} [CStarAlgebra A]

inductive Term (C : Bohr.Context A) where
  | positive : C.algebra → Term C
  | regularCover : C.algebra → Term C
  | bottom : Term C
  | top : Term C
  | join : Term C → Term C → Term C
  | meet : Term C → Term C → Term C

inductive Rule (C : Bohr.Context A) where
  | refl (P : Term C)
  | trans (P Q R : Term C)
  | bottom (P : Term C)
  | top (P : Term C)
  | joinLeft (P Q : Term C)
  | joinRight (P Q : Term C)
  | joinElim (P Q R : Term C)
  | meetLeft (P Q : Term C)
  | meetRight (P Q : Term C)
  | meetIntro (P Q R : Term C)
  | unit
  | negative (a : C.algebra)
  | negativeSquare (b : C.algebra) (hb : IsSelfAdjoint b)
  | addition (a b : C.algebra)
  | product (a b : C.algebra) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
  | productReverse (a b : C.algebra) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
  | regularity (a : C.algebra)
  | shift (a : C.algebra) (q : ℚ) (hq : 0 < q)

abbrev presentation (C : Bohr.Context A) : Presentation where
  Judgment := Term C × Term C
  Rule := Rule C
  arity := fun | .trans .. | .joinElim .. | .meetIntro .. => 2 | _ => 0
  premise := fun
    | .trans P Q R => fun i => if i = 0 then (P,Q) else (Q,R)
    | .joinElim P Q R => fun i => if i = 0 then (P,R) else (Q,R)
    | .meetIntro P Q R => fun i => if i = 0 then (P,Q) else (P,R)
    | .refl .. | .bottom .. | .top .. | .joinLeft .. | .joinRight ..
    | .meetLeft .. | .meetRight .. | .unit | .negative .. | .negativeSquare ..
    | .addition .. | .product .. | .productReverse .. | .regularity .. | .shift .. => Fin.elim0
  conclusion := fun
    | .refl P => (P,P)
    | .trans P _ R => (P,R)
    | .bottom P => (.bottom,P)
    | .top P => (P,.top)
    | .joinLeft P Q => (P,.join P Q)
    | .joinRight P Q => (Q,.join P Q)
    | .joinElim P Q R => (.join P Q,R)
    | .meetLeft P Q => (.meet P Q,P)
    | .meetRight P Q => (.meet P Q,Q)
    | .meetIntro P Q R => (P,.meet Q R)
    | .unit => (.top,.positive 1)
    | .negative a => (.meet (.positive a) (.positive (-a)),.bottom)
    | .negativeSquare b _ => (.positive (-(b*b)),.bottom)
    | .addition a b => (.positive (a+b),.join (.positive a) (.positive b))
    | .product a b _ _ => (.positive (a*b),
        .join (.meet (.positive a) (.positive b)) (.meet (.positive (-a)) (.positive (-b))))
    | .productReverse a b _ _ =>
        (.join (.meet (.positive a) (.positive b)) (.meet (.positive (-a)) (.positive (-b))),
         .positive (a*b))
    | .regularity a => (.positive a,.regularCover a)
    | .shift a q _ => (.positive (a-(q:ℂ)•1),.regularCover a)

def eval (C : Bohr.Context A) : Term C → TopologicalSpace.Opens C.Spectrum
  | .positive a => C.positiveOpen a
  | .regularCover a => ⨆ q : {q : ℚ // 0 < q}, C.shiftedPositiveOpen a q.val
  | .bottom => ⊥
  | .top => ⊤
  | .join P Q => eval C P ⊔ eval C Q
  | .meet P Q => eval C P ⊓ eval C Q

/-- Every generating relation is checked in the actual character spectrum. -/
def model (C : Bohr.Context A) : Model (presentation C) where
  Carrier j := eval C j.1 ≤ eval C j.2
  operation := fun r h => by
    cases r with
    | refl P => exact le_rfl
    | trans P Q R => exact (h 0).trans (h 1)
    | bottom P => exact bot_le
    | top P => exact le_top
    | joinLeft P Q => exact le_sup_left
    | joinRight P Q => exact le_sup_right
    | joinElim P Q R => exact sup_le (h 0) (h 1)
    | meetLeft P Q => exact inf_le_left
    | meetRight P Q => exact inf_le_right
    | meetIntro P Q R => exact le_inf (h 0) (h 1)
    | unit => exact le_of_eq (C.positiveOpen_one.symm)
    | negative a => exact le_of_eq (C.positiveOpen_neg_disjoint a)
    | negativeSquare b hb => exact le_of_eq (C.positiveOpen_neg_square b hb)
    | addition a b => exact C.positiveOpen_add_le a b
    | product a b ha hb => exact le_of_eq (C.positiveOpen_mul a b ha hb)
    | productReverse a b ha hb => exact le_of_eq (C.positiveOpen_mul a b ha hb).symm
    | regularity a => exact le_of_eq (C.positiveOpen_regular a)
    | shift a q hq => exact le_iSup (fun q : {q : ℚ // 0 < q} => C.shiftedPositiveOpen a q.val) ⟨q,hq⟩

theorem sound (C : Bohr.Context A) {Γ : Logic.Context (presentation C)} {j}
    (d : Derivation (presentation C) Γ j)
    (h : ∀ i, (model C).Carrier (Γ.claim i)) : (model C).Carrier j := d.eval (model C) h

theorem interpretation_substitute (C : Bohr.Context A)
    {Γ Δ : Logic.Context (presentation C)} {j} (d : Derivation (presentation C) Γ j)
    (r : ∀ i, Derivation (presentation C) Δ (Γ.claim i))
    (h : ∀ i, (model C).Carrier (Δ.claim i)) :
    (d.substitute r).eval (model C) h =
      d.eval (model C) (fun i => (r i).eval (model C) h) :=
  Derivation.eval_substitute (model C) h d r

/-- A composite derivation: positivity of a sum is covered by the two regular covers. -/
def additionCoverProof (C : Bohr.Context A) (a b : C.algebra) :
    Derivation (presentation C) (Logic.Context.empty (presentation C))
      (.positive (a+b), .join (.regularCover a) (.regularCover b)) :=
  by
    apply Derivation.apply (T := presentation C) (.trans (.positive (a+b)) (.join (.positive a) (.positive b))
      (.join (.regularCover a) (.regularCover b)))
    intro i
    change Fin 2 at i
    by_cases hi : i = 0
    · subst i
      exact .apply (T := presentation C) (.addition a b) (fun i => Fin.elim0 i)
    · have hi1 : i = 1 := by omega
      subst i
      apply Derivation.apply (T := presentation C) (.joinElim (.positive a) (.positive b) (.join (.regularCover a) (.regularCover b)))
      intro j
      change Fin 2 at j
      by_cases hj : j = 0
      · subst j
        apply Derivation.apply (T := presentation C) (.trans (.positive a) (.regularCover a) (.join (.regularCover a) (.regularCover b)))
        intro k
        change Fin 2 at k
        by_cases hk : k = 0
        · subst k
          exact .apply (T := presentation C) (.regularity a) (fun i => Fin.elim0 i)
        · have hk1 : k = 1 := by omega
          subst k
          exact .apply (T := presentation C) (.joinLeft _ _) (fun i => Fin.elim0 i)
      · have hj1 : j = 1 := by omega
        subst j
        apply Derivation.apply (T := presentation C) (.trans (.positive b) (.regularCover b) (.join (.regularCover a) (.regularCover b)))
        intro k
        change Fin 2 at k
        by_cases hk : k = 0
        · subst k
          exact .apply (T := presentation C) (.regularity b) (fun i => Fin.elim0 i)
        · have hk1 : k = 1 := by omega
          subst k
          exact .apply (T := presentation C) (.joinRight _ _) (fun i => Fin.elim0 i)

/-- Context extension changes the observable coefficients of the syntax. -/
def transportTerm {C D : Bohr.Context A} (h : C ≤ D) : Term C → Term D
  | .positive a => .positive (Bohr.Context.inclusion h a)
  | .regularCover a => .regularCover (Bohr.Context.inclusion h a)
  | .bottom => .bottom
  | .top => .top
  | .join P Q => .join (transportTerm h P) (transportTerm h Q)
  | .meet P Q => .meet (transportTerm h P) (transportTerm h Q)

/-- Local spectral interpretation commutes with context extension, including
 the specified countable regular cover. This does not assert that arbitrary
 continuous preimages preserve Heyting implication. -/
theorem eval_transport {C D : Bohr.Context A} (h : C ≤ D) (P : Term C) :
    eval D (transportTerm h P) = Bohr.Context.transportOpen h (eval C P) := by
  induction P with
  | positive a => exact (Bohr.Context.transport_positiveOpen h a).symm
  | regularCover a =>
    change (⨆ q : {q : ℚ // 0 < q}, D.shiftedPositiveOpen (Bohr.Context.inclusion h a) q.val) =
      (TopologicalSpace.Opens.comap (Bohr.Context.restrict h))
        (⨆ q : {q : ℚ // 0 < q}, C.shiftedPositiveOpen a q.val)
    rw [map_iSup]
    congr 1
  | bottom => exact (map_bot (TopologicalSpace.Opens.comap (Bohr.Context.restrict h))).symm
  | top => exact (map_top (TopologicalSpace.Opens.comap (Bohr.Context.restrict h))).symm
  | join P Q ihP ihQ =>
    change _ ⊔ _ = (TopologicalSpace.Opens.comap (Bohr.Context.restrict h)) (_ ⊔ _)
    rw [map_sup, ihP, ihQ]
    rfl
  | meet P Q ihP ihQ =>
    change _ ⊓ _ = (TopologicalSpace.Opens.comap (Bohr.Context.restrict h)) (_ ⊓ _)
    rw [map_inf, ihP, ihQ]
    rfl

end
end Foundation.Quantum.Bohr.GeneratorLogic
