import Foundation.Crypto.Logic.MultiDerivation

namespace CryptoLogic

open scoped ENNReal
universe u v w a b

variable {L : MultiLanguage.{a, b}} {S : MultiSignature.{u, v, w} L}
variable {Γ : Context S.unary}

/-- Each occurrence of a hypothesis has its own composed transformation and
exact family certificate. Occurrences are never silently merged. -/
structure BranchLeaf (Γ : Context S.unary) (X : L.unary.Object)
    (F : InstanceFamily (S.unary.interpret X).goal) where
  index : Fin Γ.length
  transform : CertifiedTransform (S.unary.interpret X) (S.unary.interpret (Γ[index]).object)
  family_eq : transform.transform.mapFamily F = (Γ[index]).family

namespace BranchLeaf

def prepend {X Y F} (t : CertifiedTransform (S.unary.interpret X) (S.unary.interpret Y))
    (leaf : BranchLeaf Γ Y (t.transform.mapFamily F)) : BranchLeaf Γ X F :=
  ⟨leaf.index, t.comp leaf.transform, leaf.family_eq⟩

theorem halts {X F} (leaf : BranchLeaf Γ X F) (p : BoundedProgram) (input : List Bool) :
    Machine.HaltsWithin (leaf.transform.compiler.run p.program) input
      (leaf.transform.budget p input.length) := leaf.transform.halts p input

theorem polynomialTime {X F} (leaf : BranchLeaf Γ X F) (p : BoundedProgram) :
    Machine.PolynomialTime (leaf.transform.compiler.run p.program) :=
  (leaf.transform.runBounded p).polynomialTime

end BranchLeaf

/-- Quantitative loss retains the same branch structure as the derivation. -/
inductive LossTree (length : Nat) where
  | hypothesis (i : Fin length)
  | unary (loss : AdvantageBound) (child : LossTree length)
  | binary (left right : AdvantageBound) (l r : LossTree length)

namespace LossTree

def eval {length} (t : LossTree length) (ε : Fin length → Nat → ℝ≥0∞) (n : Nat) : ℝ≥0∞ :=
  match t with
  | .hypothesis i => ε i n
  | .unary loss t => loss.eval n (t.eval ε n)
  | .binary left right l r => left.eval n (l.eval ε n) + right.eval n (r.eval ε n)

def substitute {length targetLength} (t : LossTree length)
    (f : Fin length → LossTree targetLength) : LossTree targetLength :=
  match t with
  | .hypothesis i => f i
  | .unary loss t => .unary loss (t.substitute f)
  | .binary left right l r => .binary left right (l.substitute f) (r.substitute f)

theorem eval_substitute {length targetLength} (t : LossTree length)
    (f : Fin length → LossTree targetLength) (ε) (n) :
    (t.substitute f).eval ε n = t.eval (fun i m => (f i).eval ε m) n := by
  induction t with
  | hypothesis i => rfl
  | unary loss t ih => simp [substitute, eval, ih]
  | binary left right l r hl hr => simp [substitute, eval, hl, hr]

end LossTree

namespace MultiTree

def extract {X F} : MultiTree S Γ X F → List (BranchLeaf Γ X F)
  | .hypothesis i => [⟨i, CertifiedTransform.ofReduction (CertifiedReduction.id _), rfl⟩]
  | .transport r _ child =>
    child.extract.map (BranchLeaf.prepend (CertifiedTransform.ofReduction (r.eval S.unary)))
  | .binary e _ l r =>
    (l.extract.map (BranchLeaf.prepend (S.binary e).left)) ++
      (r.extract.map (BranchLeaf.prepend (S.binary e).right))

-- The two family-map APIs are definitionally equal after unfolding. Allow
-- that unfolding during tactic matching; the kernel still checks the proof.
set_option backward.isDefEq.respectTransparency false in
theorem extract_compilers {X F} (t : MultiTree S Γ X F) :
    t.extract.map (fun leaf => (leaf.index, leaf.transform.compiler)) = t.plan.paths := by
  induction t with
  | hypothesis i => rfl
  | transport r F child ih =>
    simp only [extract, plan, CompilerTree.paths]
    rw [← ih]
    generalize child.extract = leaves
    induction leaves with
    | nil => rfl
    | cons leaf leaves ih =>
      simp only [List.map_cons]
      rw [ih]
      congr 1
      change (leaf.index, Machine.ProgramCompiler.comp (r.eval S.unary).compiler leaf.transform.compiler) =
        (leaf.index, Machine.ProgramCompiler.comp r.compiler leaf.transform.compiler)
      rw [r.eval_compiler S.unary]
  | binary e F l r hl hr =>
    simp only [extract, plan, CompilerTree.paths, List.map_append, List.map_map]
    rw [← hl, ← hr]
    simp [List.map_map, Function.comp_def, BranchLeaf.prepend, CertifiedTransform.comp,
      S.left_compiler e, S.right_compiler e]

def loss {X F} : MultiTree S Γ X F → LossTree Γ.length
  | .hypothesis i => .hypothesis i
  | .transport r _ child => .unary (r.eval S.unary).reduction.loss child.loss
  | .binary e _ l r => .binary (S.binary e).leftLoss (S.binary e).rightLoss l.loss r.loss

theorem loss_negligible {X F} (t : MultiTree S Γ X F)
    (ε : Fin Γ.length → Nat → ℝ≥0∞) (hε : ∀ i, Negligible (ε i)) :
    Negligible (fun n => t.loss.eval ε n) := by
  induction t with
  | hypothesis i => exact hε i
  | transport r F child ih => exact (r.eval S.unary).negligible _ ih
  | binary e F l r hl hr =>
    exact ((S.binary e).leftNegligible _ hl).add ((S.binary e).rightNegligible _ hr)

/-- Concrete bounds may be supplied per hypothesis. Soundness itself does not
require one bound uniform over all admissible adversaries. -/
theorem advantage_le {X F} (t : MultiTree S Γ X F)
    (ε : Fin Γ.length → Nat → ℝ≥0∞)
    (hε : ∀ i, BoundedByOnWithin (S.unary.interpret (Γ[i]).object).goal
      (S.unary.interpret (Γ[i]).object).adversaries (Γ[i]).family (ε i)) :
    ∀ A, (S.unary.interpret X).adversaries.admissible F A →
      ∀ n, advantageProfile (S.unary.interpret X).goal F A n ≤ t.loss.eval ε n := by
  induction t with
  | hypothesis i => exact hε i
  | transport r F child ih =>
    intro A hA n
    exact ((r.eval S.unary).reduction.advantageProfile_le F A n).trans
      ((r.eval S.unary).reduction.loss.monotone n
        (ih _ ((r.eval S.unary).admissibility.preserves F A hA) n))
  | binary e F l r hl hr =>
    intro A hA n
    exact ((S.binary e).advantage_le F A n).trans (add_le_add
      ((S.binary e).leftLoss.monotone n (hl _ ((S.binary e).left.admissible F A hA) n))
      ((S.binary e).rightLoss.monotone n (hr _ ((S.binary e).right.admissible F A hA) n)))

theorem loss_substitute {Δ : Context S.unary} {X F} (t : MultiTree S Γ X F)
    (f : ∀ i : Fin Γ.length, MultiTree S Δ (Γ[i]).object (Γ[i]).family) :
    (t.substitute f).loss = t.loss.substitute (fun i => (f i).loss) := by
  induction t with
  | hypothesis i => rfl
  | transport r F child ih => simp [MultiTree.substitute, loss, LossTree.substitute, ih]
  | binary e F l r hl hr => simp [MultiTree.substitute, loss, LossTree.substitute, hl, hr]

end MultiTree

namespace MultiDerivation

noncomputable def extract {X F} (d : MultiDerivation S Γ X F) : List (BranchLeaf Γ X F) :=
  d.checkedTree.extract

noncomputable def loss {X F} (d : MultiDerivation S Γ X F) : LossTree Γ.length :=
  d.checkedTree.loss

theorem advantage_le {X F} (d : MultiDerivation S Γ X F)
    (ε : Fin Γ.length → Nat → ℝ≥0∞)
    (hε : ∀ i, BoundedByOnWithin (S.unary.interpret (Γ[i]).object).goal
      (S.unary.interpret (Γ[i]).object).adversaries (Γ[i]).family (ε i))
    (A) (hA : (S.unary.interpret X).adversaries.admissible F A) (n) :
    advantageProfile (S.unary.interpret X).goal F A n ≤ d.loss.eval ε n :=
  d.checkedTree.advantage_le ε hε A hA n

theorem extract_compilers {X F} (d : MultiDerivation S Γ X F) :
    d.extract.map (fun leaf => (leaf.index, leaf.transform.compiler)) = d.plan.paths := by
  rw [extract, d.checkedTree.extract_compilers, d.checkedTree_plan]

/-- The emitted pure plan is exactly the code certified at each leaf. -/
theorem extract_run {X F} (d : MultiDerivation S Γ X F) (p : Machine.Program) :
    d.extract.map (fun leaf => (leaf.index, leaf.transform.compiler.run p)) = d.plan.run p := by
  rw [CompilerTree.run, ← d.extract_compilers, List.map_map]
  rfl

theorem extract_emitted {X F} (d : MultiDerivation S Γ X F) (p : Machine.Program) :
    d.extract.map (fun leaf => (leaf.index.val, leaf.transform.compiler.run p)) = d.run p := by
  rw [d.run_eq, ← d.extract_run, List.map_map]
  rfl

noncomputable def runBounded {X F} (d : MultiDerivation S Γ X F) (p : BoundedProgram) :
    List (Fin Γ.length × BoundedProgram) :=
  d.extract.map fun leaf => (leaf.index, leaf.transform.runBounded p)

theorem runBounded_programs {X F} (d : MultiDerivation S Γ X F) (p : BoundedProgram) :
    (d.runBounded p).map (fun (i, q) => (i, q.program)) = d.plan.run p.program := by
  rw [runBounded, List.map_map]
  exact d.extract_run p.program

@[macro_inline] def substitute {Δ : Context S.unary} {X F} (d : MultiDerivation S Γ X F)
    (f : ∀ i : Fin Γ.length, MultiDerivation S Δ (Γ[i]).object (Γ[i]).family) :
    MultiDerivation S Δ X F where
  plan := d.plan.substitute (fun i => (f i).plan)
  compilers := d.compilers.flatMap fun (i, c) =>
    (f i).compilers.map fun (j, k) => (j, .comp c k)
  emitted_eq := by
    intro p
    rw [CompilerTree.run_substitute, ← d.emitted_eq p]
    simp only [List.map_flatMap, List.flatMap_map]
    apply List.flatMap_congr
    intro entry _
    rcases entry with ⟨i, c⟩
    rw [List.map_map]
    simpa only [Function.comp_def, Machine.ProgramCompiler.run] using (f i).emitted_eq (c.run p)
  typed := by
    classical
    obtain ⟨t, h⟩ := d.typed
    choose trees hs using (fun i => (f i).typed)
    refine ⟨t.substitute trees, ?_⟩
    rw [MultiTree.plan_substitute, h]
    congr 1
    exact funext hs

theorem substitute_run {Δ : Context S.unary} {X F} (d : MultiDerivation S Γ X F)
    (f : ∀ i : Fin Γ.length, MultiDerivation S Δ (Γ[i]).object (Γ[i]).family) (p) :
    (d.substitute f).plan.run p = (d.plan.run p).flatMap fun (i, q) => (f i).plan.run q :=
  d.plan.run_substitute (fun i => (f i).plan) p

end MultiDerivation
end CryptoLogic
