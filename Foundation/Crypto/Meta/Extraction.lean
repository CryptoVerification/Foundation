import Foundation.Crypto.Logic.Derivation

namespace CryptoLogic

universe u v w a b

variable {L : Language.{a, b}} {S : Signature.{u, v, w} L} {Γ : Context S}

/-- The exact hypothesis used by a derivation, together with its resource-
certified reduction and the equality identifying the target instance family. -/
structure Extraction (Γ : Context S) (X : L.Object)
    (F : InstanceFamily (S.interpret X).goal) where
  index : Fin Γ.length
  certificate : CertifiedReduction (S.interpret X) (S.interpret (Γ[index]).object)
  family_eq : certificate.reduction.mapFamily F = (Γ[index]).family

namespace Extraction

/-- Reindex only along a proved equality of context positions. -/
def reindex {X F} (e : Extraction Γ X F) (i : Fin Γ.length) (h : e.index = i) :
    Extraction Γ X F where
  index := i
  certificate := by cases h; exact e.certificate
  family_eq := by cases h; exact e.family_eq

theorem reindex_compiler {X F} (e : Extraction Γ X F) (i : Fin Γ.length) (h : e.index = i) :
    (e.reindex i h).certificate.compiler = e.certificate.compiler := by
  cases h
  rfl

end Extraction

namespace DerivationTree

/-- Structural interpretation retains a single used hypothesis, the emitted
compiler, the stopping budgets, and the quantitative advantage loss. -/
def extract {X F} : DerivationTree S Γ X F → Extraction Γ X F
  | .hypothesis i => ⟨i, CertifiedReduction.id _, rfl⟩
  | .transport r F premise =>
      let e := premise.extract
      ⟨e.index, (r.eval S).comp e.certificate, e.family_eq⟩

theorem extract_compiler {X F} (d : DerivationTree S Γ X F) :
    d.extract.certificate.compiler = d.compiler := by
  induction d with
  | hypothesis i => rfl
  | transport r F premise ih =>
      change Machine.ProgramCompiler.comp (r.eval S).compiler premise.extract.certificate.compiler =
        Machine.ProgramCompiler.comp r.compiler premise.compiler
      rw [r.eval_compiler S, ih]

theorem extract_index {X F} (d : DerivationTree S Γ X F) :
    d.extract.index = d.code.selected := by
  induction d with
  | hypothesis i => rfl
  | transport r F premise ih => exact ih

end DerivationTree

namespace Derivation

/-- Recover semantic evidence only for analysis, never for executable code
construction. The selected index is computed from the pure syntax below. -/
noncomputable def checkedTree {X F} (d : Derivation S Γ X F) : DerivationTree S Γ X F :=
  Classical.choose d.typed

theorem checkedTree_code {X F} (d : Derivation S Γ X F) :
    d.checkedTree.code = d.code := Classical.choose_spec d.typed

noncomputable def extract {X F} (d : Derivation S Γ X F) : Extraction Γ X F :=
  d.checkedTree.extract.reindex d.code.selected
    (by rw [d.checkedTree.extract_index, d.checkedTree_code])

theorem extract_index {X F} (d : Derivation S Γ X F) :
    d.extract.index = d.code.selected := rfl

/-- Substitution tracks the selected replacement's hypothesis exactly. -/
theorem extract_index_substitute {Δ : Context S} {X F} (d : Derivation S Γ X F)
    (replacement : ∀ i : Fin Γ.length,
      Derivation S Δ (Γ[i]).object (Γ[i]).family) :
    (d.substitute replacement).extract.index = (replacement d.extract.index).extract.index :=
  d.code.selected_substitute (fun i => (replacement i).code)

theorem extract_compiler {X F} (d : Derivation S Γ X F) :
    d.extract.certificate.compiler = d.compiler := by
  calc
    d.extract.certificate.compiler = d.checkedTree.extract.certificate.compiler :=
      Extraction.reindex_compiler _ _ _
    _ = d.checkedTree.compiler := d.checkedTree.extract_compiler
    _ = d.compiler := by
      rw [← d.checkedTree.code_compiler, d.checkedTree_code]
      exact d.compiler_eq.symm

/-- Apply the extracted certificate to an actual source stopping witness. -/
noncomputable def runBounded {X F} (d : Derivation S Γ X F) (p : BoundedProgram) : BoundedProgram :=
  d.extract.certificate.runBounded p

theorem runBounded_program {X F} (d : Derivation S Γ X F) (p : BoundedProgram) :
    (d.runBounded p).program = d.compiler.run p.program := by
  change d.extract.certificate.compiler.run p.program = d.compiler.run p.program
  rw [d.extract_compiler]

theorem compiler_halts {X F} (d : Derivation S Γ X F) (p : BoundedProgram)
    (input : List Bool) :
    Machine.HaltsWithin (d.compiler.run p.program) input
      ((d.runBounded p).budget input.length) := by
  rw [← d.runBounded_program p]
  exact (d.runBounded p).halts input

theorem compiler_polynomialTime {X F} (d : Derivation S Γ X F) (p : BoundedProgram) :
    Machine.PolynomialTime (d.compiler.run p.program) := by
  rw [← d.runBounded_program p]
  exact (d.runBounded p).polynomialTime

/-- The returned target witness realizes the transformed adversary, belongs
to the target class, and carries a polynomial bound for the emitted code. -/
noncomputable def mapWitness {X F} (d : Derivation S Γ X F)
    {A : AdversaryFamily (S.interpret X).goal F}
    (p : (S.interpret X).Witness F A) :
    (S.interpret (Γ[d.extract.index]).object).Witness
      (d.extract.certificate.reduction.mapFamily F)
      (d.extract.certificate.reduction.mapAdversaryFamily F A) :=
  d.extract.certificate.mapWitness p

theorem mapWitness_program {X F} (d : Derivation S Γ X F)
    {A : AdversaryFamily (S.interpret X).goal F}
    (p : (S.interpret X).Witness F A) :
    (d.mapWitness p).bounded.program = d.compiler.run p.bounded.program :=
  d.runBounded_program p.bounded

/-- The quantitative inequality is retained, rather than only the qualitative
fact that the source is secure whenever the selected target hypothesis is. -/
theorem advantage_le {X F} (d : Derivation S Γ X F)
    (A : AdversaryFamily (S.interpret X).goal F) (n : Nat) :
    advantageProfile (S.interpret X).goal F A n ≤
      d.extract.certificate.reduction.loss.eval n
        (advantageProfile (S.interpret (Γ[d.extract.index]).object).goal
          (d.extract.certificate.reduction.mapFamily F)
          (d.extract.certificate.reduction.mapAdversaryFamily F A) n) :=
  d.extract.certificate.reduction.advantageProfile_le F A n

/-- Every derivation uses a context position; there are no closed derivations
in this fragment. This is syntactic, not a claim that security is impossible. -/
theorem no_empty {X F} (d : Derivation S [] X F) : False :=
  Fin.elim0 d.extract.index

end Derivation
end CryptoLogic
