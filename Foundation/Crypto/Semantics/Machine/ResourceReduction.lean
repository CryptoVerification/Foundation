import Foundation.Crypto.Semantics.Machine.ResourceSecurity
import Foundation.Crypto.Semantics.Machine.CertifiedReduction

/-! Uniform resource certificates for concrete security transport. A certificate
is indexed by source and target resource bounds. It covers every source program
with the source stopping bound, rather than one chosen adversary. -/

open scoped ENNReal

universe u v w a b c d e f

namespace Reduction

open Machine

/-- The emitted code realizes the semantic reduction and satisfies one common
target resource bound. External adapter costs and oracle query counts remain
outside this one-request machine certificate. -/
structure ResourceProgramReduction
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    (r : Reduction P Q)
    (JP : MachineAdversaryInterface.{u, a, b} P)
    (JQ : MachineAdversaryInterface.{v, c, d} Q)
    (source target : ResourceBounds) where
  compiler : ProgramCompiler
  halts : ∀ (p : Program),
    (∀ input : List Bool, HaltsWithin p input (source.steps input.length)) →
    ∀ input : List Bool,
      HaltsWithin (compiler.run p) input (target.steps input.length)
  realizes : ∀ (F : InstanceFamily P) (A : AdversaryFamily P F) (p : Program),
    (∀ input : List Bool, HaltsWithin p input (source.steps input.length)) →
    JP.Realizes F p source.steps A →
    JQ.Realizes (r.mapFamily F) (compiler.run p) target.steps
      (r.mapAdversaryFamily F A)
  inputLength : ∀ (F : InstanceFamily P),
    (∀ n (request : JP.Request n (F n)),
      (JP.machineInput n (F n) request).length ≤ source.inputLength n) →
    ∀ n (request : JQ.Request n (r.mapFamily F n)),
      (JQ.machineInput n (r.mapFamily F n) request).length ≤ target.inputLength n

namespace ResourceProgramReduction

variable {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
  {r : Reduction P Q}
  {JP : MachineAdversaryInterface.{u, a, b} P}
  {JQ : MachineAdversaryInterface.{v, c, d} Q}
  {source target : ResourceBounds}

/-- The existential target program is exactly the compiler's output. -/
theorem mapWithin (T : r.ResourceProgramReduction JP JQ source target)
    {F : InstanceFamily P} {A : AdversaryFamily P F}
    (h : JP.Within source F A) :
    JQ.Within target (r.mapFamily F) (r.mapAdversaryFamily F A) := by
  obtain ⟨p, hHalts, hSize, hRealizes⟩ := h
  exact ⟨T.compiler.run p, T.halts p hHalts,
    T.inputLength F hSize, T.realizes F A p hHalts hRealizes⟩

/-- Concrete security transport needs monotonicity of advantage loss, but
does not require polynomial resources or negligibility preservation. -/
theorem resourceSecure (T : r.ResourceProgramReduction JP JQ source target)
    (F : InstanceFamily P) (ε : Nat → ℝ≥0∞)
    (h : JQ.ResourceSecure target (r.mapFamily F) ε) :
    JP.ResourceSecure source F (fun n => r.loss.eval n (ε n)) := by
  intro A hA n
  exact (r.advantageProfile_le F A n).trans
    (r.loss.monotone n (h _ (T.mapWithin hA) n))

theorem resourceSecure_affine (T : r.ResourceProgramReduction JP JQ source target)
    (F : InstanceFamily P) (coefficient : Nat → Nat) (error ε : Nat → ℝ≥0∞)
    (hLoss : r.loss = AdvantageBound.affine coefficient error)
    (h : JQ.ResourceSecure target (r.mapFamily F) ε) :
    JP.ResourceSecure source F
      (fun n => (coefficient n : ℝ≥0∞) * ε n + error n) := by
  simpa only [hLoss, AdvantageBound.affine] using T.resourceSecure F ε h

def id (J : MachineAdversaryInterface.{u, a, b} P) (R : ResourceBounds) :
    (Reduction.id P).ResourceProgramReduction J J R R where
  compiler := .identity
  halts := by intro p h; exact h
  realizes := by intro F A p _ h; exact h
  inputLength := by intro F h; exact h

/-- Resource bounds follow source-to-target composition. Advantage losses
apply the second loss first, then the first loss, as in `Reduction.comp`. -/
def comp {S : CryptoGoal.{w}}
    {s : Reduction Q S} {JS : MachineAdversaryInterface.{w, e, f} S}
    {final : ResourceBounds}
    (T : r.ResourceProgramReduction JP JQ source target)
    (U : s.ResourceProgramReduction JQ JS target final) :
    (r.comp s).ResourceProgramReduction JP JS source final where
  compiler := .comp T.compiler U.compiler
  halts := by
    intro p h
    exact U.halts (T.compiler.run p) (T.halts p h)
  realizes := by
    intro F A p hHalts hRealizes
    exact U.realizes (r.mapFamily F) (r.mapAdversaryFamily F A)
      (T.compiler.run p) (T.halts p hHalts)
      (T.realizes F A p hHalts hRealizes)
  inputLength := by
    intro F h
    exact U.inputLength (r.mapFamily F) (T.inputLength F h)

theorem comp_run {S : CryptoGoal.{w}}
    {s : Reduction Q S} {JS : MachineAdversaryInterface.{w, e, f} S}
    {final : ResourceBounds}
    (T : r.ResourceProgramReduction JP JQ source target)
    (U : s.ResourceProgramReduction JQ JS target final) (p : Program) :
    (T.comp U).compiler.run p = U.compiler.run (T.compiler.run p) := rfl

/-- Reuse an existing simulation with explicit common time and input bounds.
The source stopping budget is fixed before quantifying over programs. -/
def ofSimulation (T : r.MachineProgramSimulation JP JQ)
    (source target : ResourceBounds)
    (hBudget : ∀ m, T.transformBudget source.steps m ≤ target.steps m)
    (hSize : ∀ (F : InstanceFamily P),
      (∀ n (request : JP.Request n (F n)),
        (JP.machineInput n (F n) request).length ≤ source.inputLength n) →
      ∀ n (request : JQ.Request n (r.mapFamily F n)),
        (JQ.machineInput n (r.mapFamily F n) request).length ≤ target.inputLength n) :
    r.ResourceProgramReduction JP JQ source target where
  compiler := T.compiler
  halts := by
    intro p h input
    exact (T.halts p source.steps h input).mono (hBudget _)
  realizes := by
    intro F A p hHalts hRealizes
    have hOld := T.halts p source.steps hHalts
    have hNew : ∀ input : List Bool,
        HaltsWithin (T.compiler.run p) input (target.steps input.length) :=
      fun input => (hOld input).mono (hBudget _)
    exact (JQ.realizeFamily_budget_eq_of_halts (r.mapFamily F) (T.compiler.run p)
      (T.transformBudget source.steps) target.steps hOld hNew).symm.trans
      (T.realizes F A p source.steps hHalts hRealizes)
  inputLength := hSize

end ResourceProgramReduction
end Reduction

namespace CryptoLogic.CertifiedReduction

open Machine

/-- Connect the small logic's existing certificate to common resource bounds.
Only the source step budget must be polynomial to form a `BoundedProgram`.
The explicit majorant obligation is not inferred from individual polynomiality. -/
def uniformResources {X Y : CryptoLogic.SecurityObject.{u, v, w}}
    (r : CryptoLogic.CertifiedReduction X Y) (source target : ResourceBounds)
    (hSource : PolynomiallyBounded source.steps)
    (hBudget : ∀ p : CryptoLogic.BoundedProgram, p.budget = source.steps →
      ∀ m, r.budget p m ≤ target.steps m)
    (hSize : ∀ (F : InstanceFamily X.goal),
      (∀ n (request : X.interface.Request n (F n)),
        (X.interface.machineInput n (F n) request).length ≤ source.inputLength n) →
      ∀ n (request : Y.interface.Request n (r.reduction.mapFamily F n)),
        (Y.interface.machineInput n (r.reduction.mapFamily F n) request).length ≤
          target.inputLength n) :
    r.reduction.ResourceProgramReduction X.interface Y.interface source target where
  compiler := r.compiler
  halts := by
    intro p h input
    let bounded : CryptoLogic.BoundedProgram := ⟨p, source.steps, hSource, h⟩
    exact (r.halts bounded input).mono (hBudget bounded rfl _)
  realizes := by
    intro F A p hHalts hRealizes
    let bounded : CryptoLogic.BoundedProgram := ⟨p, source.steps, hSource, hHalts⟩
    have hNew : ∀ input : List Bool,
        HaltsWithin (r.compiler.run p) input (target.steps input.length) :=
      fun input => (r.halts bounded input).mono (hBudget bounded rfl _)
    exact (Y.interface.realizeFamily_budget_eq_of_halts (r.reduction.mapFamily F)
      (r.compiler.run p) (r.budget bounded) target.steps (r.halts bounded) hNew).symm.trans
      (r.realizes F A bounded hRealizes)
  inputLength := hSize

end CryptoLogic.CertifiedReduction
