import Foundation.Crypto.Logic.General.Derivation

namespace CryptoLogic.General

universe u v a b

set_option backward.isDefEq.respectTransparency false

variable {K : CodeSystem} {L : Language.{a, b} K} {S : Signature.{u, v} L}

/-- A typed certificate for each hypothesis occurrence. The target code type
is the exact machine attached to that context position. -/
structure BranchLeaf (Γ : Context S) (X : L.Object)
    (F : InstanceFamily (S.interpret X).goal) where
  index : Fin Γ.length
  transform : CertifiedTransform (S.interpret X) (S.interpret (Γ.claim index).object)
  family_eq : transform.transform.mapFamily F = (Γ.claim index).family

namespace BranchLeaf

variable {Γ : Context S}

def prepend {X Y F} (T : CertifiedTransform (S.interpret X) (S.interpret Y))
    (leaf : BranchLeaf Γ Y (T.transform.mapFamily F)) : BranchLeaf Γ X F :=
  ⟨leaf.index, T.comp leaf.transform, leaf.family_eq⟩

def packedCompiler {X F} (leaf : BranchLeaf Γ X F) : Plan.Path K Γ.length (L.machine X) :=
  (leaf.index, ⟨L.machine (Γ.claim leaf.index).object, leaf.transform.compiler⟩)

def emitted {X F} (leaf : BranchLeaf Γ X F) (code : K.Code (L.machine X)) : Plan.Output K Γ.length :=
  (leaf.index, ⟨L.machine (Γ.claim leaf.index).object, leaf.transform.compiler.run code⟩)

/-- Full execution guarantees are retained in the backend's original units. -/
theorem compiler_executes {X F} (leaf : BranchLeaf Γ X F) (A)
    (W : (S.interpret X).Witness F A) :
    (S.interpret (Γ.claim leaf.index).object).execution.ExecutesWithin
      (leaf.transform.transform.mapFamily F) (leaf.transform.compiler.run W.code)
      (leaf.transform.mapWitness F A W).resources := leaf.transform.compiler_executes F A W

theorem compiler_realizes {X F} (leaf : BranchLeaf Γ X F) (A)
    (W : (S.interpret X).Witness F A) :
    (S.interpret (Γ.claim leaf.index).object).execution.Realizes
      (leaf.transform.transform.mapFamily F) (leaf.transform.transform.mapAdversaryFamily F A)
      (leaf.transform.compiler.run W.code) (leaf.transform.mapWitness F A W).resources :=
  leaf.transform.compiler_realizes F A W

end BranchLeaf

namespace Tree

variable {Γ Δ : Context S}

def extract {X F} : Tree S Γ X F → List (BranchLeaf Γ X F)
  | .hypothesis i => [⟨i, CertifiedTransform.id _, rfl⟩]
  | .transport r _ child => child.extract.map (BranchLeaf.prepend (r.eval S).toTransform)
  | .binary e _ left right =>
      (left.extract.map (BranchLeaf.prepend (S.binary e).left)) ++
      (right.extract.map (BranchLeaf.prepend (S.binary e).right))

theorem extract_compilers {X F} (tree : Tree S Γ X F) :
    tree.extract.map BranchLeaf.packedCompiler = tree.plan.paths := by
  induction tree with
  | hypothesis i => rfl
  | transport r F child ih =>
      simp only [extract, plan, Plan.paths_unary, List.map_map]
      rw [← ih, List.map_map]
      congr 1
      funext leaf
      change (leaf.index, (⟨L.machine (Γ.claim leaf.index).object,
        Compiler.comp (r.eval S).compiler leaf.transform.compiler⟩ : Sigma (Compiler K _))) =
        (leaf.index, (⟨L.machine (Γ.claim leaf.index).object,
          Compiler.comp r.compiler leaf.transform.compiler⟩ : Sigma (Compiler K _)))
      rw [r.eval_compiler S]
  | binary e F left right hl hr =>
      simp only [extract, plan, Plan.paths_binary, List.map_append, List.map_map]
      rw [← hl, ← hr, List.map_map, List.map_map]
      apply congrArg₂ (· ++ ·)
      · apply List.map_congr_left
        intro leaf _
        change (leaf.index, (⟨L.machine (Γ.claim leaf.index).object,
          Compiler.comp (S.binary e).left.compiler leaf.transform.compiler⟩ : Sigma (Compiler K _))) =
          (leaf.index, (⟨L.machine (Γ.claim leaf.index).object,
            Compiler.comp (L.binaryCompilers e).1 leaf.transform.compiler⟩ : Sigma (Compiler K _)))
        rw [S.left_compiler e]
      · apply List.map_congr_left
        intro leaf _
        change (leaf.index, (⟨L.machine (Γ.claim leaf.index).object,
          Compiler.comp (S.binary e).right.compiler leaf.transform.compiler⟩ : Sigma (Compiler K _))) =
          (leaf.index, (⟨L.machine (Γ.claim leaf.index).object,
            Compiler.comp (L.binaryCompilers e).2 leaf.transform.compiler⟩ : Sigma (Compiler K _)))
        rw [S.right_compiler e]

def loss {X F} : Tree S Γ X F → CryptoLogic.LossTree Γ.length
  | .hypothesis i => .hypothesis i
  | .transport r _ child => .unary (r.eval S).reduction.loss child.loss
  | .binary e _ left right => .binary (S.binary e).leftLoss (S.binary e).rightLoss left.loss right.loss

theorem loss_negligible {X F} (tree : Tree S Γ X F) (ε) (hε : ∀ i, Negligible (ε i)) :
    Negligible (fun n => tree.loss.eval ε n) := by
  induction tree with
  | hypothesis i => exact hε i
  | transport r F child ih => exact (r.eval S).negligible _ ih
  | binary e F left right hl hr =>
      exact ((S.binary e).leftNegligible _ hl).add ((S.binary e).rightNegligible _ hr)

theorem advantage_le {X F} (tree : Tree S Γ X F) (ε)
    (hε : ∀ i, BoundedByOnWithin (S.interpret (Γ.claim i).object).goal
      (S.interpret (Γ.claim i).object).adversaries (Γ.claim i).family (ε i)) :
    ∀ A, (S.interpret X).adversaries.admissible F A →
      ∀ n, advantageProfile (S.interpret X).goal F A n ≤ tree.loss.eval ε n := by
  induction tree with
  | hypothesis i => exact hε i
  | transport r F child ih =>
      intro A hA n
      exact ((r.eval S).reduction.advantageProfile_le F A n).trans
        ((r.eval S).reduction.loss.monotone n
          (ih _ ((r.eval S).toTransform.admissible F A hA) n))
  | binary e F left right hl hr =>
      intro A hA n
      exact ((S.binary e).advantage_le F A n).trans (add_le_add
        ((S.binary e).leftLoss.monotone n (hl _ ((S.binary e).left.admissible F A hA) n))
        ((S.binary e).rightLoss.monotone n (hr _ ((S.binary e).right.admissible F A hA) n)))

theorem loss_substitute {X F} (tree : Tree S Γ X F)
    (replacement : ∀ i, Tree S Δ (Γ.claim i).object (Γ.claim i).family) :
    (tree.substitute replacement).loss = tree.loss.substitute (fun i => (replacement i).loss) := by
  induction tree with
  | hypothesis i => rfl
  | transport r F child ih => simp only [substitute, loss, CryptoLogic.LossTree.substitute, ih]
  | binary e F left right hl hr => simp only [substitute, loss, CryptoLogic.LossTree.substitute, hl, hr]

end Tree

namespace Derivation

variable {Γ Δ : Context S}

noncomputable def extract {X F} (d : Derivation S Γ X F) : List (BranchLeaf Γ X F) := d.checkedTree.extract
noncomputable def loss {X F} (d : Derivation S Γ X F) : CryptoLogic.LossTree Γ.length := d.checkedTree.loss

theorem extract_compilers {X F} (d : Derivation S Γ X F) :
    d.extract.map BranchLeaf.packedCompiler = d.plan.paths := by
  rw [extract, d.checkedTree.extract_compilers, d.checkedTree_plan]

/-- The generated heterogeneous output list is exactly the certified list. -/
theorem extract_run {X F} (d : Derivation S Γ X F) (code : K.Code (L.machine X)) :
    d.extract.map (fun leaf => leaf.emitted code) = d.plan.run code := by
  rw [← d.plan.paths_run code, ← d.extract_compilers, List.map_map]
  rfl

theorem extract_emitted {X F} (d : Derivation S Γ X F) (code : K.Code (L.machine X)) :
    d.extract.map (fun leaf => (leaf.index.val, (leaf.emitted code).2)) = d.run code := by
  rw [d.run_eq, ← d.extract_run, List.map_map]
  rfl

theorem advantage_le {X F} (d : Derivation S Γ X F) (ε)
    (hε : ∀ i, BoundedByOnWithin (S.interpret (Γ.claim i).object).goal
      (S.interpret (Γ.claim i).object).adversaries (Γ.claim i).family (ε i))
    (A) (hA : (S.interpret X).adversaries.admissible F A) (n) :
    advantageProfile (S.interpret X).goal F A n ≤ d.loss.eval ε n :=
  d.checkedTree.advantage_le ε hε A hA n

end Derivation
end CryptoLogic.General
