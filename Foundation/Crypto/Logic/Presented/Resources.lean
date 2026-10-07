import Foundation.Crypto.Logic.Presented.Reconstruction

/-! Code extraction and quantitative security for the reconstructed calculus.
Analysis uses the caller's explicit interpreted tree, never an arbitrary tree
selected from an existential certificate. Each output retains the backend's
original resource type, stopping proof, and distribution realization. -/
namespace CryptoLogic.Presented

open General
open scoped ENNReal
universe u v a b p
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace Interpretation

variable {K : CodeSystem} {L : General.Language.{a, b} K}
  {P : Parameters.{a, b, p} L} {S : General.Signature.{u, v} L}

def analysis (M : Interpretation P S) {Γ : Presented.Context P} {X F}
    (d : Presented.Derivation P Γ X F) : General.Derivation.Analysis (M.legacy d) :=
  ⟨M.tree d, M.tree_plan d⟩

def loss (M : Interpretation P S) {Γ : Presented.Context P} {X F}
    (d : Presented.Derivation P Γ X F) : CryptoLogic.LossTree Γ.length := (M.tree d).loss

theorem bounded (M : Interpretation P S) {Γ : Presented.Context P} {X F}
    (d : Presented.Derivation P Γ X F) (ε)
    (hε : ∀ i, (S.interpret (Γ.claim i).object).Bounded (M.family (Γ.claim i).family) (ε i)) :
    (S.interpret X).Bounded (M.family F) (fun n => (M.loss d).eval ε n) :=
  (M.tree d).advantage_le ε hε

theorem loss_substitute (M : Interpretation P S) {Γ Δ : Presented.Context P}
    {A : Claim P} (d : Foundation.Logic.Derivation (presentation P) Γ A)
    (replacement : ∀ i, Foundation.Logic.Derivation (presentation P) Δ (Γ.claim i)) :
    M.loss (d.substitute replacement) =
      (M.loss d).substitute (fun i => M.loss (replacement i)) := by
  rw [loss, M.tree_substitute, General.Tree.loss_substitute]
  rfl

theorem loss_negligible (M : Interpretation P S) {Γ : Presented.Context P} {X F}
    (d : Presented.Derivation P Γ X F) (ε) (hε : ∀ i, Negligible (ε i)) :
    Negligible (fun n => (M.loss d).eval ε n) := (M.tree d).loss_negligible ε hε

def runWitnesses (M : Interpretation P S) {Γ : Presented.Context P} {X F}
    (d : Presented.Derivation P Γ X F) (A)
    (W : (S.interpret X).Witness (M.family F) A) : List (General.CertifiedOutput (M.context Γ)) :=
  (M.analysis d).runWitnesses A W

/-- Every actual emitted code is the code in the full resource certificate. -/
theorem runWitnesses_emitted (M : Interpretation P S) {Γ : Presented.Context P} {X F}
    (d : Presented.Derivation P Γ X F) (A)
    (W : (S.interpret X).Witness (M.family F) A) :
    (M.runWitnesses d A W).map General.CertifiedOutput.emitted = Presented.Derivation.run d W.code := by
  rw [runWitnesses, General.Derivation.Analysis.runWitnesses_emitted, M.legacy_run]

theorem extract_emitted (M : Interpretation P S) {Γ : Presented.Context P} {X F}
    (d : Presented.Derivation P Γ X F) (code : K.Code (L.machine X)) :
    (M.tree d).extract.map (fun leaf => (leaf.index.val, (leaf.emitted code).2)) =
      Presented.Derivation.run d code := by
  rw [← M.legacy_run d code]
  exact (M.analysis d).extract_emitted code

end Interpretation

theorem quote_loss {K : CodeSystem} {L : General.Language.{a, b} K}
    {S : General.Signature.{u, v} L} {Γ : General.Context S} {X F}
    (t : General.Tree S Γ X F) : (interpretation S).loss (quote t) = t.loss := by
  rw [Interpretation.loss, tree_quote]

/-- Reconstruction preserves the full dependent certificate list: resource
values, stopping proofs and probability-distribution realizations included. -/
theorem quote_runWitnesses {K : CodeSystem} {L : General.Language.{a, b} K}
    {S : General.Signature.{u, v} L} {Γ : General.Context S} {X F}
    (t : General.Tree S Γ X F) (A) (W : (S.interpret X).Witness F A) :
    (interpretation S).runWitnesses (quote t) A W =
      (General.Derivation.ofTreeAnalysis t).runWitnesses A W := by
  change (General.Derivation.ofTreeAnalysis ((interpretation S).tree (quote t))).runWitnesses A W = _
  rw [tree_quote]

end CryptoLogic.Presented
