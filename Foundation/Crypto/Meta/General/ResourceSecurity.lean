import Foundation.Crypto.Meta.General.Extraction

/-! Concrete security and executable-output certificates for every backend.
Resource bounds are those of the security objects; no common time unit is
introduced. An explicit analysis tree preserves the selected loss certificate. -/
namespace CryptoLogic.General

universe u v a b
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace SecurityObject

variable {K : CodeSystem} {m : K.Machine}

/-- A common advantage bound inside the object's certified resource class. -/
def Bounded (X : SecurityObject.{u, v} K m) (F : InstanceFamily X.goal)
    (ε : Nat → ℝ≥0∞) : Prop := BoundedByOnWithin X.goal X.adversaries F ε

theorem Bounded.mono {X : SecurityObject.{u, v} K m} {F ε δ}
    (h : X.Bounded F ε) (hεδ : ∀ n, ε n ≤ δ n) : X.Bounded F δ := by
  intro A hA n
  exact (h A hA n).trans (hεδ n)

theorem Bounded.asymptotic {X : SecurityObject.{u, v} K m} {F ε}
    (h : X.Bounded F ε) (hε : Negligible ε) : X.Secure F :=
  SecureOnWithin.of_boundedBy h hε

namespace Witness

def reindex {X : SecurityObject.{u, v} K m} {F G : InstanceFamily X.goal}
    {A : AdversaryFamily X.goal F} (W : X.Witness F A) (h : F = G) :
    Sigma (fun B : AdversaryFamily X.goal G => X.Witness G B) :=
  h ▸ ⟨A, W⟩

@[simp] theorem reindex_code {X : SecurityObject.{u, v} K m} {F G : InstanceFamily X.goal}
    {A : AdversaryFamily X.goal F} (W : X.Witness F A) (h : F = G) :
    (W.reindex h).2.code = W.code := by cases h; rfl

end Witness

end SecurityObject

namespace CertifiedReduction

variable {K : CodeSystem} {m n : K.Machine}
  {X : SecurityObject.{u, v} K m} {Y : SecurityObject.{u, v} K n}

theorem bounded (T : CertifiedReduction X Y) (F ε)
    (h : Y.Bounded (T.reduction.mapFamily F) ε) :
    X.Bounded F (fun n => T.reduction.loss.eval n (ε n)) := by
  intro A hA n
  exact (T.reduction.advantageProfile_le F A n).trans
    (T.reduction.loss.monotone n (h _ (T.toTransform.admissible F A hA) n))

end CertifiedReduction

namespace CertifiedBinaryReduction

variable {K : CodeSystem} {m n k : K.Machine}
  {X : SecurityObject.{u, v} K m} {Y : SecurityObject.{u, v} K n}
  {Z : SecurityObject.{u, v} K k}

theorem bounded (T : CertifiedBinaryReduction X Y Z) (F ε δ)
    (hY : Y.Bounded (T.left.transform.mapFamily F) ε)
    (hZ : Z.Bounded (T.right.transform.mapFamily F) δ) :
    X.Bounded F (fun n => T.leftLoss.eval n (ε n) + T.rightLoss.eval n (δ n)) := by
  intro A hA n
  exact (T.advantage_le F A n).trans (add_le_add
    (T.leftLoss.monotone n (hY _ (T.left.admissible F A hA) n))
    (T.rightLoss.monotone n (hZ _ (T.right.admissible F A hA) n)))

end CertifiedBinaryReduction

variable {K : CodeSystem} {L : Language.{a, b} K} {S : Signature.{u, v} L}

/-- A target adversary and its full backend-specific execution certificate,
indexed by the original context position. Repeated positions are retained. -/
structure CertifiedOutput (Γ : Context S) where
  index : Fin Γ.length
  adversary : AdversaryFamily (S.interpret (Γ.claim index).object).goal (Γ.claim index).family
  witness : (S.interpret (Γ.claim index).object).Witness (Γ.claim index).family adversary

namespace CertifiedOutput

variable {Γ : Context S}

def emitted (out : CertifiedOutput Γ) : Nat × Sigma K.Code :=
  (out.index.val, ⟨L.machine (Γ.claim out.index).object, out.witness.code⟩)

end CertifiedOutput

namespace BranchLeaf

variable {Γ : Context S}

/-- Transport to the precise context family, without weakening the resource
bound or discarding the realization and admissibility proofs. -/
def runWitness {X F} (leaf : BranchLeaf Γ X F) (A)
    (W : (S.interpret X).Witness F A) : CertifiedOutput Γ := by
  let target := (leaf.transform.mapWitness F A W).reindex leaf.family_eq
  exact ⟨leaf.index, target.1, target.2⟩

theorem runWitness_emitted {Γ : Context S} {X F} (leaf : BranchLeaf Γ X F) (A)
    (W : (S.interpret X).Witness F A) :
    (leaf.runWitness A W).emitted = (leaf.index.val, (leaf.emitted W.code).2) := by
  change (leaf.index.val, (⟨L.machine (Γ.claim leaf.index).object,
      ((leaf.transform.mapWitness F A W).reindex leaf.family_eq).2.code⟩ : Sigma K.Code)) = _
  rw [SecurityObject.Witness.reindex_code, leaf.transform.code_eq]
  rfl

end BranchLeaf

namespace Derivation

variable {Γ Δ : Context S}

noncomputable def runWitnesses {X F} (d : Derivation S Γ X F) (A)
    (W : (S.interpret X).Witness F A) : List (CertifiedOutput Γ) :=
  d.extract.map fun leaf => leaf.runWitness A W

theorem runWitnesses_emitted {X F} (d : Derivation S Γ X F) (A)
    (W : (S.interpret X).Witness F A) :
    (d.runWitnesses A W).map CertifiedOutput.emitted = d.run W.code := by
  rw [runWitnesses, List.map_map, ← d.extract_emitted W.code]
  apply List.map_congr_left
  intro leaf _
  exact leaf.runWitness_emitted A W

theorem bounded {X F} (d : Derivation S Γ X F) (ε)
    (hε : ∀ i, (S.interpret (Γ.claim i).object).Bounded (Γ.claim i).family (ε i)) :
    (S.interpret X).Bounded F (fun n => d.loss.eval ε n) := d.advantage_le ε hε

theorem loss_negligible {X F} (d : Derivation S Γ X F) (ε)
    (hε : ∀ i, Negligible (ε i)) : Negligible (fun n => d.loss.eval ε n) :=
  d.checkedTree.loss_negligible ε hε

/-- Cut/substitution preserves the typed sequential interpretation of every
leaf, including machine changes and repeated uses of one hypothesis. -/
theorem substitute_run {X F} (d : Derivation S Γ X F)
    (replacement : ∀ i, Derivation S Δ (Γ.claim i).object (Γ.claim i).family)
    (code : K.Code (L.machine X)) :
    (d.substitute replacement).run code =
      (d.plan.runWith (fun i => (replacement i).plan) code).map
        (fun (i, packed) => (i.val, packed)) := by
  rw [run_eq, substitute, Plan.run_substitute]

/-- Choice selects an analysis, but callers may supply a particular registered
tree when they need its exact loss expression rather than an arbitrary one. -/
structure Analysis {X F} (d : Derivation S Γ X F) where
  tree : Tree S Γ X F
  plan_eq : tree.plan = d.plan

namespace Analysis

variable {X F} {d : Derivation S Γ X F}

def loss (analysis : Analysis d) : CryptoLogic.LossTree Γ.length := analysis.tree.loss

theorem bounded (analysis : Analysis d) (ε)
    (hε : ∀ i, (S.interpret (Γ.claim i).object).Bounded (Γ.claim i).family (ε i)) :
    (S.interpret X).Bounded F (fun n => analysis.loss.eval ε n) :=
  analysis.tree.advantage_le ε hε

theorem extract_emitted (analysis : Analysis d) (code : K.Code (L.machine X)) :
    analysis.tree.extract.map (fun leaf => (leaf.index.val, (leaf.emitted code).2)) = d.run code := by
  rw [d.run_eq, ← analysis.plan_eq, ← analysis.tree.plan.paths_run, ← analysis.tree.extract_compilers]
  simp only [List.map_map]
  rfl

def substitute (analysis : Analysis d)
    (replacement : ∀ i, Derivation S Δ (Γ.claim i).object (Γ.claim i).family)
    (analyses : ∀ i, Analysis (replacement i)) : Analysis (d.substitute replacement) where
  tree := analysis.tree.substitute (fun i => (analyses i).tree)
  plan_eq := by
    rw [Tree.plan_substitute, analysis.plan_eq]
    change d.plan.substitute _ = d.plan.substitute _
    congr 1
    exact funext (fun i => (analyses i).plan_eq)

theorem loss_substitute (analysis : Analysis d)
    (replacement : ∀ i, Derivation S Δ (Γ.claim i).object (Γ.claim i).family)
    (analyses : ∀ i, Analysis (replacement i)) :
    (analysis.substitute replacement analyses).loss =
      analysis.loss.substitute (fun i => (analyses i).loss) :=
  analysis.tree.loss_substitute _

def runWitnesses (analysis : Analysis d) (A)
    (W : (S.interpret X).Witness F A) : List (CertifiedOutput Γ) :=
  analysis.tree.extract.map fun leaf => leaf.runWitness A W

theorem runWitnesses_emitted (analysis : Analysis d) (A)
    (W : (S.interpret X).Witness F A) :
    (analysis.runWitnesses A W).map CertifiedOutput.emitted = d.run W.code := by
  rw [runWitnesses, List.map_map, ← analysis.extract_emitted W.code]
  apply List.map_congr_left
  intro leaf _
  exact leaf.runWitness_emitted A W

theorem loss_negligible (analysis : Analysis d) (ε) (hε : ∀ i, Negligible (ε i)) :
    Negligible (fun n => analysis.loss.eval ε n) := analysis.tree.loss_negligible ε hε

end Analysis
end Derivation
end CryptoLogic.General
