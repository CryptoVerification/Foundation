import Foundation.Crypto.Meta.Soundness

namespace CryptoLogic

universe u v w a b

variable {L : Language.{a, b}} {S : Signature.{u, v, w} L} {Γ : Context S}

namespace Extraction

theorem reindex_budget {X F} (e : Extraction Γ X F) (i : Fin Γ.length)
    (h : e.index = i) (p : BoundedProgram) (m : Nat) :
    (e.reindex i h).certificate.budget p m = e.certificate.budget p m := by
  cases h
  rfl

theorem reindex_loss {X F} (e : Extraction Γ X F) (i : Fin Γ.length)
    (h : e.index = i) :
    (e.reindex i h).certificate.reduction.loss = e.certificate.reduction.loss := by
  cases h
  rfl

end Extraction

/-- A single registered reduction to one context hypothesis, with the exact
instance-family equality needed to use that hypothesis. -/
structure NormalForm (S : Signature.{u, v, w} L) (Γ : Context S)
    (X : L.Object) (F : InstanceFamily (S.interpret X).goal) where
  index : Fin Γ.length
  route : ReductionExpr L X (Γ[index]).object
  family_eq : (route.eval S).reduction.mapFamily F = (Γ[index]).family

namespace DerivationTree

/-- Collapse all transport nodes, retaining the original association of
certificates. The terminal identity retains even the hypothesis-only case. -/
def route {X F} (d : DerivationTree S Γ X F) :
    ReductionExpr L X (Γ[d.extract.index]).object :=
  match d with
  | .hypothesis i => .identity (Γ[i]).object
  | .transport r _ premise => .seq r premise.route

/-- This is equality of the whole certificate, including budget and loss,
not only equality of emitted machine programs. -/
theorem route_eval {X F} (d : DerivationTree S Γ X F) :
    d.route.eval S = d.extract.certificate := by
  induction d with
  | hypothesis i => rfl
  | transport r F premise ih =>
      change (r.eval S).comp (premise.route.eval S) =
        (r.eval S).comp premise.extract.certificate
      rw [ih]

def normalForm {X F} (d : DerivationTree S Γ X F) : NormalForm S Γ X F where
  index := d.extract.index
  route := d.route
  family_eq := by rw [d.route_eval]; exact d.extract.family_eq

theorem normalForm_compiler {X F} (d : DerivationTree S Γ X F) :
    d.normalForm.route.compiler = d.compiler := by
  rw [← d.normalForm.route.eval_compiler S]
  exact (congrArg CertifiedReduction.compiler d.route_eval).trans d.extract_compiler

end DerivationTree

namespace NormalForm

/-- Reconstruct a derivation with exactly one transport above one hypothesis. -/
@[macro_inline] def toDerivation {X F} (n : NormalForm S Γ X F) :
    Derivation S Γ X F where
  code := .transport n.route (.hypothesis n.index)
  compiler := .comp n.route.compiler .identity
  compiler_eq := rfl
  typed := by
    have hypothesis : ∃ t : DerivationTree S Γ (Γ[n.index]).object
        ((n.route.eval S).reduction.mapFamily F), t.code = .hypothesis n.index := by
      rw [n.family_eq]
      exact ⟨.hypothesis n.index, rfl⟩
    obtain ⟨t, h⟩ := hypothesis
    exact ⟨.transport n.route F t, congrArg (DerivationSyntax.transport n.route) h⟩

theorem toDerivation_run {X F} (n : NormalForm S Γ X F) (p : Machine.Program) :
    n.toDerivation.compiler.run p = n.route.compiler.run p := rfl

end NormalForm

namespace DerivationSyntax

/-- Substitution is sequential code composition with the replacement of the
selected hypothesis. Unselected replacement compilers have no effect. -/
theorem compiler_substitute_run {length targetLength}
    (d : DerivationSyntax L length)
    (replacement : Fin length → DerivationSyntax L targetLength) (p : Machine.Program) :
    (d.substitute replacement).compiler.run p =
      (replacement d.selected).compiler.run (d.compiler.run p) := by
  induction d generalizing p with
  | hypothesis i => rfl
  | transport r premise ih =>
      exact ih (r.compiler.run p)

end DerivationSyntax

namespace Derivation

/-- Analysis of an already certified executable derivation. Recovering its
semantic tree uses choice; the original executable compiler is unaffected. -/
noncomputable def normalForm {X F} (d : Derivation S Γ X F) : NormalForm S Γ X F :=
  d.checkedTree.normalForm

theorem normalForm_index {X F} (d : Derivation S Γ X F) :
    d.normalForm.index = d.extract.index := by
  change d.checkedTree.extract.index = d.code.selected
  rw [d.checkedTree.extract_index, d.checkedTree_code]

theorem normalForm_compiler {X F} (d : Derivation S Γ X F) :
    d.normalForm.route.compiler = d.compiler := by
  rw [normalForm, d.checkedTree.normalForm_compiler,
    ← d.checkedTree.code_compiler, d.checkedTree_code, ← d.compiler_eq]

theorem normalForm_run {X F} (d : Derivation S Γ X F) (p : Machine.Program) :
    d.normalForm.toDerivation.compiler.run p = d.compiler.run p := by
  rw [NormalForm.toDerivation_run, d.normalForm_compiler]

/-- The recovered route preserves the exact stopping bound of the checked
tree, with no reassociation or replacement by a coarser majorant. -/
theorem normalForm_budget {X F} (d : Derivation S Γ X F) (p : BoundedProgram) (m : Nat) :
    (d.normalForm.route.eval S).budget p m = (d.runBounded p).budget m := by
  change (d.checkedTree.route.eval S).budget p m = d.extract.certificate.budget p m
  rw [d.checkedTree.route_eval]
  exact (Extraction.reindex_budget _ _ _ p m).symm

theorem normalForm_loss {X F} (d : Derivation S Γ X F) :
    (d.normalForm.route.eval S).reduction.loss = d.extract.certificate.reduction.loss := by
  change (d.checkedTree.route.eval S).reduction.loss = d.extract.certificate.reduction.loss
  rw [d.checkedTree.route_eval]
  exact (Extraction.reindex_loss _ _ _).symm

/-- Eliminating an intermediate assumption preserves the order of the two
emitted programs and selects exactly the dependency used by the first proof. -/
theorem substitute_run {Δ : Context S} {X F} (d : Derivation S Γ X F)
    (replacement : ∀ i : Fin Γ.length,
      Derivation S Δ (Γ[i]).object (Γ[i]).family) (p : Machine.Program) :
    (d.substitute replacement).compiler.run p =
      (replacement d.extract.index).compiler.run (d.compiler.run p) := by
  change (d.code.substitute (fun i => (replacement i).code)).compiler.run p =
    (replacement d.code.selected).compiler.run (d.compiler.run p)
  rw [d.compiler_eq, (replacement d.code.selected).compiler_eq]
  exact d.code.compiler_substitute_run (fun i => (replacement i).code) p

end Derivation

/-- Relative completeness: derivability is exactly reachability of one
hypothesis by registered reduction syntax at the required instance family.
This does not assert completeness for all semantically true security claims. -/
theorem derivable_iff_registered_route {X F} :
    Nonempty (Derivation S Γ X F) ↔
      ∃ i : Fin Γ.length, ∃ r : ReductionExpr L X (Γ[i]).object,
        (r.eval S).reduction.mapFamily F = (Γ[i]).family := by
  constructor
  · rintro ⟨d⟩
    exact ⟨d.normalForm.index, d.normalForm.route, d.normalForm.family_eq⟩
  · rintro ⟨i, r, h⟩
    exact ⟨(NormalForm.mk i r h).toDerivation⟩

end CryptoLogic
