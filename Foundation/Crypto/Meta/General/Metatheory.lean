import Foundation.Crypto.Meta.General.ResourceSecurity

/-! The erased program plan, its registered typed proof, and the emitted
execution witnesses agree. Completeness here is only relative to registered
inference trees, not to arbitrary semantic security implications. -/
namespace CryptoLogic.General

universe u v a b
set_option backward.isDefEq.respectTransparency false
variable {K : CodeSystem} {L : Language.{a, b} K} {S : Signature.{u, v} L}

namespace Plan

variable {length : Nat} {machines : Fin length → K.Machine}

theorem run_ne_nil {m} (plan : Plan K machines m) (code : K.Code m) : plan.run code ≠ [] := by
  induction plan with
  | hypothesis i m h => exact List.cons_ne_nil _ _
  | unary c child ih => exact ih (c.run code)
  | binary c d left right hl hr =>
      intro h
      exact hl (c.run code) (List.append_eq_nil_iff.mp h).1

end Plan

namespace Derivation

variable {Γ : Context S}

/-- Reify a registered typed tree into the same executable-plan API. The
semantic tree can be noncomputable; its code is then an analysis artifact. -/
@[macro_inline] def ofTree {X F} (tree : Tree S Γ X F) : Derivation S Γ X F where
  plan := tree.plan
  compilers := tree.plan.paths
  emitted_eq := Plan.paths_run _
  typed := ⟨tree, rfl⟩

def ofTreeAnalysis {X F} (tree : Tree S Γ X F) : Analysis (ofTree tree) := ⟨tree, rfl⟩

theorem run_ne_nil {X F} (d : Derivation S Γ X F) (code : K.Code (L.machine X)) :
    d.run code ≠ [] := by
  rw [d.run_eq]
  intro h
  exact d.plan.run_ne_nil code (List.map_eq_nil_iff.mp h)

theorem run_length {X F} (d : Derivation S Γ X F) (code : K.Code (L.machine X)) :
    (d.run code).length = d.extract.length := by
  rw [← d.extract_emitted code, List.length_map]

theorem runWitnesses_length {X F} (d : Derivation S Γ X F) (A)
    (W : (S.interpret X).Witness F A) :
    (d.runWitnesses A W).length = (d.run W.code).length := by
  rw [runWitnesses, List.length_map, d.run_length]

theorem runWitnesses_ne_nil {X F} (d : Derivation S Γ X F) (A)
    (W : (S.interpret X).Witness F A) : d.runWitnesses A W ≠ [] := by
  intro h
  have he := d.runWitnesses_emitted A W
  rw [h, List.map_nil] at he
  exact d.run_ne_nil W.code he.symm

end Derivation

/-- The constructive direction reifies the registered tree; the reverse
recovers its typing evidence. Binary branches remain part of the tree. -/
theorem derivable_iff_registered_tree {Γ : Context S} {X F} :
    Nonempty (Derivation S Γ X F) ↔ Nonempty (Tree S Γ X F) := by
  constructor
  · rintro ⟨d⟩
    obtain ⟨tree, _⟩ := d.typed
    exact ⟨tree⟩
  · rintro ⟨tree⟩
    exact ⟨Derivation.ofTree tree⟩

end CryptoLogic.General
