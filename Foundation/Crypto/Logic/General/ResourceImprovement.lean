import Foundation.Crypto.Meta.General.ResourceSecurity
import Foundation.Crypto.Logic.General.ExecutionRefinement

/-! Directed resource improvement of implementations of a fixed adversary
transformation. Resource orders remain backend-specific. Postcomposition
requires resource monotonicity: execution/realization certificates alone do
not imply it. Unlike structural tracks, improvement is not closed by inverse.
All certificates refer to the code actually emitted by the implementation. -/
namespace CryptoLogic.General.ResourceImprovement

universe u v
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
variable {K : CodeSystem} {m n k l : K.Machine}
  {X : SecurityObject.{u, v} K m} {Y : SecurityObject.{u, v} K n}
  {Z : SecurityObject.{u, v} K k} {V : SecurityObject.{u, v} K l}

def identitySemantic (X : SecurityObject.{u, v} K m) : AdversaryTransform X.goal X.goal :=
  ⟨fun I => I, fun _ A => A⟩

def composeSemantic {P Q R : CryptoGoal.{u}} (f : AdversaryTransform P Q)
    (g : AdversaryTransform Q R) : AdversaryTransform P R :=
  ⟨fun I => g.mapInstance (f.mapInstance I), fun I A => g.reduce (f.mapInstance I) (f.reduce I A)⟩

/-- Implementations share the precise instance and adversary transformation,
but may have different finite code and different resource witnesses. -/
structure Implementation (X : SecurityObject.{u, v} K m) (Y : SecurityObject.{u, v} K n)
    (semantic : AdversaryTransform X.goal Y.goal) where
  compiler : Compiler K m n
  mapWitness : ∀ F A, X.Witness F A →
    Y.Witness (semantic.mapFamily F) (semantic.mapAdversaryFamily F A)
  code_eq : ∀ F A W, (mapWitness F A W).code = compiler.run W.code

namespace Implementation
variable {f : AdversaryTransform X.goal Y.goal} {g : AdversaryTransform Y.goal Z.goal}

def ofCertified (T : CertifiedTransform X Y) : Implementation X Y T.transform :=
  ⟨T.compiler, T.mapWitness, T.code_eq⟩

def certified (I : Implementation X Y f) : CertifiedTransform X Y :=
  ⟨f, I.compiler, I.mapWitness, I.code_eq⟩

def identity (X : SecurityObject.{u, v} K m) : Implementation X X (identitySemantic X) :=
  ⟨.identity m, fun _ _ W => W, by intros; rfl⟩

def comp (I : Implementation X Y f) (J : Implementation Y Z g) :
    Implementation X Z (composeSemantic f g) where
  compiler := .comp I.compiler J.compiler
  mapWitness := fun F A W => J.mapWitness _ _ (I.mapWitness F A W)
  code_eq := by intros; rw [J.code_eq, I.code_eq]; rfl

/-- The old quantitative reduction can be equipped with the new code and its
own full execution evidence without changing its adversary or loss bound. -/
def certifyReduction (r : Reduction X.goal Y.goal)
    (I : Implementation X Y ⟨r.mapInstance, r.reduce⟩) (h : r.loss.PreservesNegligible) :
    CertifiedReduction X Y := ⟨r, I.compiler, I.mapWitness, I.code_eq, h⟩

theorem executes (I : Implementation X Y f) (F A) (W : X.Witness F A) :
    Y.execution.ExecutesWithin (f.mapFamily F) (I.compiler.run W.code)
      (I.mapWitness F A W).resources := I.certified.compiler_executes F A W

theorem realizes (I : Implementation X Y f) (F A) (W : X.Witness F A) :
    Y.execution.Realizes (f.mapFamily F) (f.mapAdversaryFamily F A)
      (I.compiler.run W.code) (I.mapWitness F A W).resources := I.certified.compiler_realizes F A W

/-- Comparison is inside Y's original resource type, at the same input
witness. It does not identify the two emitted programs. -/
def Improves [Preorder Y.execution.Resources] (better worse : Implementation X Y f) : Prop :=
  ∀ F A (W : X.Witness F A),
    (better.mapWitness F A W).resources ≤ (worse.mapWitness F A W).resources

/-- This is an additional operational contract, not a consequence of
semantic correctness. Include code size in resources when it affects cost. -/
def MonotoneResources [Preorder X.execution.Resources] [Preorder Y.execution.Resources]
    (I : Implementation X Y f) : Prop :=
  ∀ F A (W W' : X.Witness F A), W.resources ≤ W'.resources →
    (I.mapWitness F A W).resources ≤ (I.mapWitness F A W').resources

section Order
variable [Preorder Y.execution.Resources]

theorem improves_refl (I : Implementation X Y f) : Improves I I := fun _ _ _ => le_rfl

theorem improves_trans {I J H : Implementation X Y f} (h : Improves I J) (h' : Improves J H) :
    Improves I H := fun F A W => (h F A W).trans (h' F A W)

/-- Replacing a suffix needs no condition on the unchanged prefix. -/
theorem precompose {P : SecurityObject.{u, v} K l} {s : AdversaryTransform P.goal X.goal}
    (H : Implementation P X s) {I J : Implementation X Y f} (h : Improves I J) :
    Improves (H.comp I) (H.comp J) := fun F A W => h _ _ (H.mapWitness F A W)

end Order

/-- A single local improvement can be used in any certified suffix that
preserves the resource order. The two realizations still target the same A. -/
theorem postcompose [Preorder Y.execution.Resources] [Preorder Z.execution.Resources]
    {I J : Implementation X Y f} (h : Improves I J) (H : Implementation Y Z g)
    (hH : MonotoneResources H) : Improves (I.comp H) (J.comp H) :=
  fun F A W => hH _ _ (I.mapWitness F A W) (J.mapWitness F A W) (h F A W)

/-- Simultaneously replace both components of a chain. -/
theorem comp_improves [Preorder Y.execution.Resources] [Preorder Z.execution.Resources]
    {I J : Implementation X Y f} {H H' : Implementation Y Z g}
    (h : Improves I J) (h' : Improves H H') (hH : MonotoneResources H) :
    Improves (I.comp H) (J.comp H') :=
  improves_trans (postcompose h H hH) (precompose J h')

theorem comp_monotone [Preorder X.execution.Resources] [Preorder Y.execution.Resources]
    [Preorder Z.execution.Resources] (I : Implementation X Y f) (J : Implementation Y Z g)
    (hI : MonotoneResources I) (hJ : MonotoneResources J) : MonotoneResources (I.comp J) :=
  fun F A W W' h => hJ _ _ _ _ (hI F A W W' h)

/-- When resource types are partially ordered, reversible improvement forces
resource equality at every witness. Strict optimization must be directed. -/
theorem resources_eq_of_both [PartialOrder Y.execution.Resources]
    {I J : Implementation X Y f} (h : Improves I J) (h' : Improves J I) (F A)
    (W : X.Witness F A) : (I.mapWitness F A W).resources = (J.mapWitness F A W).resources :=
  le_antisymm (h F A W) (h' F A W)

/-- A resource restriction is kept inside the target's original resource
type. Code-dependent restrictions require an additional explicit premise. -/
def constrain (I : Implementation X Y f) (Q : Y.execution.Resources → Prop)
    (hQ : ∀ F A (W : X.Witness F A), Q (I.mapWitness F A W).resources) :
    Implementation X (Y.refine (fun _ _ r => Q r)) f where
  compiler := I.compiler
  mapWitness := fun F A W => SecurityObject.attach (fun _ _ r => Q r) _ _
    (I.mapWitness F A W) (hQ F A W)
  code_eq := I.code_eq

/-- Directed replacement preserves every downward-closed resource contract.
The output retains its original realization and admissibility certificate. -/
def constrainImprovement [Preorder Y.execution.Resources]
    {I J : Implementation X Y f} (h : Improves I J)
    (Q : Y.execution.Resources → Prop)
    (hDown : ∀ r s, r ≤ s → Q s → Q r)
    (hOld : ∀ F A (W : X.Witness F A), Q (J.mapWitness F A W).resources) :
    Implementation X (Y.refine (fun _ _ r => Q r)) f :=
  I.constrain Q (fun F A W => hDown _ _ (h F A W) (hOld F A W))

end Implementation

/-- Quantitative security is certified for the new actual code. Resource
improvement is a separate theorem; security does not rely on cost equality. -/
theorem optimized_bounded (r : Reduction X.goal Y.goal)
    (I : Implementation X Y ⟨r.mapInstance, r.reduce⟩) (h : r.loss.PreservesNegligible)
    (F ε) (hY : Y.Bounded (r.mapFamily F) ε) :
    X.Bounded F (fun n => r.loss.eval n (ε n)) :=
  (I.certifyReduction r h).bounded F ε hY

/-- A bounded-security assumption for the restricted target class suffices
for the optimized actual code. The original quantitative loss is retained. -/
theorem constrained_bounded [Preorder Y.execution.Resources] (r : Reduction X.goal Y.goal)
    {I J : Implementation X Y ⟨r.mapInstance, r.reduce⟩} (hIJ : I.Improves J)
    (Q : Y.execution.Resources → Prop) (hDown : ∀ r s, r ≤ s → Q s → Q r)
    (hOld : ∀ F A (W : X.Witness F A), Q (J.mapWitness F A W).resources)
    (hLoss : r.loss.PreservesNegligible) (F ε)
    (hY : (Y.refine (fun _ _ r => Q r)).Bounded (r.mapFamily F) ε) :
    X.Bounded F (fun n => r.loss.eval n (ε n)) :=
  (Implementation.certifyReduction (Y := Y.refine (fun _ _ r => Q r)) r
    (Implementation.constrainImprovement hIJ Q hDown hOld) hLoss).bounded F ε hY

end CryptoLogic.General.ResourceImprovement
