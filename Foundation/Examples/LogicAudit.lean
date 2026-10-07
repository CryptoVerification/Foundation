import Foundation.Crypto.Logic.Presented.Resources

/-! Independent checks of the calculus's logical contracts. These proofs use
only the public constructors and model interface, not the reconstruction proof.
Completeness here quantifies over all rule-preserving proposition models; it
is not completeness for cryptographic truth in one intended model. -/
namespace Foundation.Logic.Audit

universe j r
set_option linter.checkUnivs false

variable {T : Presentation.{j, r}} {Γ : Context T}

/-- A refuting model rules out a derivation, provided all hypotheses hold. -/
theorem refuting_model {A : T.Judgment} (M : Model.{j, r, 0} T)
    (environment : ∀ i, M.Carrier (Γ.claim i)) (refutes : ¬ M.Carrier A) :
    ¬ Nonempty (Derivation T Γ A) := by
  rintro ⟨d⟩
  exact refutes (d.eval M environment)

/-- Without nullary rules, no closed proof can exist. Even cycles in the
registered rules cannot manufacture a finite proof without a hypothesis. -/
theorem no_closed_without_nullary (positive : ∀ rule, 0 < T.arity rule)
    {A : T.Judgment} : ¬ Nonempty (Derivation T (Context.empty T) A) := by
  rintro ⟨d⟩
  induction d with
  | hypothesis i => exact Fin.elim0 i
  | apply rule children ih => exact ih ⟨0, positive rule⟩

/-- The model of derivability retains precisely the given rules and context. -/
noncomputable def provabilityModel (T : Presentation.{j, r}) (Γ : Context T) :
    Model.{j, r, 0} T where
  Carrier := fun A => Nonempty (Derivation T Γ A)
  operation := fun rule children =>
    ⟨Derivation.apply rule (fun i => Classical.choice (children i))⟩

/-- Soundness and completeness with respect to all proposition-valued models
of this rule presentation, with the given context as hypotheses. -/
theorem provable_iff_all_models (A : T.Judgment) :
    Nonempty (Derivation T Γ A) ↔
      ∀ M : Model.{j, r, 0} T, (∀ i, M.Carrier (Γ.claim i)) → M.Carrier A := by
  constructor
  · rintro ⟨d⟩ M environment
    exact d.eval M environment
  · intro valid
    exact valid (provabilityModel T Γ) (fun i => ⟨Derivation.hypothesis i⟩)

end Foundation.Logic.Audit

namespace CryptoLogic.Presented.Audit

universe a b p
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

/-- The current cryptographic instance contains no unconditional security
axiom. Its unary and binary rules cannot prove anything from an empty context. -/
theorem no_unconditional_derivation {K : General.CodeSystem}
    {L : General.Language.{a, b} K} (P : Parameters.{a, b, p} L) (A : Claim P) :
    ¬ Nonempty (Foundation.Logic.Derivation (presentation P)
      (Foundation.Logic.Context.empty (presentation P)) A) := by
  apply Foundation.Logic.Audit.no_closed_without_nullary
  intro rule
  cases rule with
  | transport r F => change 0 < 1; decide
  | binary e F => change 0 < 2; decide

end CryptoLogic.Presented.Audit
