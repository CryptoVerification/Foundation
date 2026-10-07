import Foundation.Crypto.Logic.Presented.Resources
import Foundation.Crypto.Logic.General.Legacy

/-! Coverage of the original single-premise and two-premise public APIs. The
existing general-machine embedding supplies the execution interpretation;
reconstruction then supplies a proof in the semantics-independent calculus. -/
namespace CryptoLogic.Presented.Legacy

universe u v w a b
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

/-- Every original two-premise derivation has a pure representative preserving
all emitted native programs and original assumption positions. -/
theorem reconstruct_multi {L : CryptoLogic.MultiLanguage.{a, b}}
    {S : CryptoLogic.MultiSignature.{u, v, w} L} {Γ : CryptoLogic.Context S.unary} {X F}
    (d : CryptoLogic.MultiDerivation S Γ X F) :
    ∃ q : Presented.Derivation (parameters (General.Legacy.signature S))
      (quoteContext (General.Legacy.context Γ)) X F,
      ∀ code, Presented.Derivation.run q code =
        (d.run code).map (fun (i, output) => (i, ⟨General.Backends.Kind.native, output⟩)) := by
  obtain ⟨q, _, hq⟩ := reconstruct (General.Legacy.derivation d)
  exact ⟨q, fun code => (hq code).trans (General.Legacy.derivation_run d code)⟩

/-- The original single-premise API is covered as well, including its selected
assumption position and composed compiler. -/
theorem reconstruct_unary {L : CryptoLogic.Language.{a, b}}
    {S : CryptoLogic.Signature.{u, v, w} L} {Γ : CryptoLogic.Context S} {X F}
    (d : CryptoLogic.Derivation S Γ X F) :
    ∃ q : Presented.Derivation
      (parameters (General.Legacy.signature (General.Legacy.Unary.signature S)))
      (quoteContext (General.Legacy.context Γ)) X F,
      ∀ code, Presented.Derivation.run q code =
        [(d.code.selected.val, ⟨General.Backends.Kind.native, d.compiler.run code⟩)] := by
  obtain ⟨q, _, hq⟩ := reconstruct (General.Legacy.Unary.derivation d)
  exact ⟨q, fun code => (hq code).trans (General.Legacy.Unary.derivation_run d code)⟩

/-- The original selected tree keeps its full quantitative loss expression. -/
theorem quote_multi_loss {L : CryptoLogic.MultiLanguage.{a, b}}
    {S : CryptoLogic.MultiSignature.{u, v, w} L} {Γ : CryptoLogic.Context S.unary} {X F}
    (t : CryptoLogic.MultiTree S Γ X F) :
    (interpretation (General.Legacy.signature S)).loss (quote (General.Legacy.tree t)) = t.loss := by
  rw [quote_loss, General.Legacy.tree_loss]

end CryptoLogic.Presented.Legacy
