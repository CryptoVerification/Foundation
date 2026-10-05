import Foundation.Crypto.Semantics.Machine.PPT
import Foundation.Crypto.Semantics.Machine.Compiler
import Foundation.Crypto.Semantics.Resource.Reduction

universe u v w a b c d e f

namespace Reduction

open Machine

/-- A certificate that a finite compiler syntax implements this reduction
relative to two finite-I/O machine adapters. The compiler reads only source
code, independent of the instance family and security parameter. Its
structurally recursive interpreter is executable; `transformBudget` is
analysis data and is not part of the emitted machine code. Semantic
preservation uses a valid all-input, all-branch source stopping budget;
arbitrary timeout budgets are not program-realization certificates. -/
structure MachineProgramTransformation
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    (R : Reduction P Q)
    (JP : MachineAdversaryInterface.{u, a, b} P)
    (JQ : MachineAdversaryInterface.{v, c, d} Q) where
  compiler : Machine.ProgramCompiler
  transformBudget : (Nat → Nat) → Nat → Nat
  coefficient : Nat
  securityDegree : Nat
  sourceDegree : Nat
  budget_bound : ∀ (q : Nat → Nat) (m : Nat),
    transformBudget q m ≤ coefficient * (m + 1) ^ securityDegree *
      (q m + 1) ^ sourceDegree
  halts : ∀ (p : Machine.Program) (q : Nat → Nat),
    (∀ input : List Bool, Machine.HaltsWithin p input (q input.length)) →
    ∀ input : List Bool,
      Machine.HaltsWithin (compiler.run p) input
        (transformBudget q input.length)
  realizes : ∀ (F : InstanceFamily P) (A : AdversaryFamily P F)
      (p : Machine.Program) (q : Nat → Nat),
    (∀ input : List Bool, Machine.HaltsWithin p input (q input.length)) →
    JP.Realizes F p q A →
    JQ.Realizes (R.mapFamily F) (compiler.run p) (transformBudget q)
      (R.mapAdversaryFamily F A)
  mapInputSize : ∀ (F : InstanceFamily P),
    JP.InputSizeBound F → JQ.InputSizeBound (R.mapFamily F)
  size_polynomial : ∀ (F : InstanceFamily P)
      (size : JP.InputSizeBound F),
    PolynomiallyBounded size.limit →
      PolynomiallyBounded (mapInputSize F size).limit

/-- The finite compiler, its worst-case step bound, and semantic correctness
without an all-request source input-size map. This is the certificate needed
for protocols such as two-stage IND-CPA, whose arbitrary caller-supplied
state makes `JP.InputSizeBound` impossible. Input-size obligations are
supplied separately when deriving a target PPT class. The same-input
`budget_bound` is an additional certificate: polynomiality of `q` alone does
not control `q` at larger subroutine inputs from its value at the original
input length. A compiler must justify that bound for its actual calls. -/
structure MachineProgramSimulation
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    (R : Reduction P Q)
    (JP : MachineAdversaryInterface.{u, a, b} P)
    (JQ : MachineAdversaryInterface.{v, c, d} Q) where
  compiler : Machine.ProgramCompiler
  transformBudget : (Nat → Nat) → Nat → Nat
  coefficient : Nat
  securityDegree : Nat
  sourceDegree : Nat
  budget_bound : ∀ (q : Nat → Nat) (m : Nat),
    transformBudget q m ≤ coefficient * (m + 1) ^ securityDegree *
      (q m + 1) ^ sourceDegree
  halts : ∀ (p : Machine.Program) (q : Nat → Nat),
    (∀ input : List Bool, Machine.HaltsWithin p input (q input.length)) →
    ∀ input : List Bool,
      Machine.HaltsWithin (compiler.run p) input
        (transformBudget q input.length)
  realizes : ∀ (F : InstanceFamily P) (A : AdversaryFamily P F)
      (p : Machine.Program) (q : Nat → Nat),
    (∀ input : List Bool, Machine.HaltsWithin p input (q input.length)) →
    JP.Realizes F p q A →
    JQ.Realizes (R.mapFamily F) (compiler.run p) (transformBudget q)
      (R.mapAdversaryFamily F A)

namespace MachineProgramSimulation

def transform
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    {R : Reduction P Q}
    {JP : MachineAdversaryInterface.{u, a, b} P}
    {JQ : MachineAdversaryInterface.{v, c, d} Q}
    (T : R.MachineProgramSimulation JP JQ) :
    Machine.Program → Machine.Program := T.compiler.run

theorem budget_polynomiallyBounded
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    {R : Reduction P Q}
    {JP : MachineAdversaryInterface.{u, a, b} P}
    {JQ : MachineAdversaryInterface.{v, c, d} Q}
    (T : R.MachineProgramSimulation JP JQ)
    {q : Nat → Nat} (hq : PolynomiallyBounded q) :
    PolynomiallyBounded (T.transformBudget q) := by
  have hqPlus : PolynomiallyBounded (fun m => q m + 1) :=
    hq.add (PolynomiallyBounded.const 1)
  have hmPlus : PolynomiallyBounded (fun m => m + 1) :=
    PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)
  have hmajor : PolynomiallyBounded (fun m =>
      T.coefficient * (m + 1) ^ T.securityDegree *
        (q m + 1) ^ T.sourceDegree) :=
    ((PolynomiallyBounded.const T.coefficient).mul
      (hmPlus.pow T.securityDegree)).mul (hqPlus.pow T.sourceDegree)
  exact PolynomiallyBounded.mono (T.budget_bound q) hmajor

theorem preservesPolynomialTime
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    {R : Reduction P Q}
    {JP : MachineAdversaryInterface.{u, a, b} P}
    {JQ : MachineAdversaryInterface.{v, c, d} Q}
    (T : R.MachineProgramSimulation JP JQ)
    {p : Machine.Program} (hp : Machine.PolynomialTime p) :
    Machine.PolynomialTime (T.transform p) := by
  obtain ⟨q, hq, hHalts⟩ := hp
  exact ⟨T.transformBudget q, T.budget_polynomiallyBounded hq,
    T.halts p q hHalts⟩

end MachineProgramSimulation

namespace MachineProgramTransformation

/-- Forget the input-size mapping while retaining executable code,
operational bounds, and simulation correctness. -/
def toSimulation
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    {R : Reduction P Q}
    {JP : MachineAdversaryInterface.{u, a, b} P}
    {JQ : MachineAdversaryInterface.{v, c, d} Q}
    (T : R.MachineProgramTransformation JP JQ) :
    R.MachineProgramSimulation JP JQ where
  compiler := T.compiler
  transformBudget := T.transformBudget
  coefficient := T.coefficient
  securityDegree := T.securityDegree
  sourceDegree := T.sourceDegree
  budget_bound := T.budget_bound
  halts := T.halts
  realizes := T.realizes

/-- Execute the finite compiler syntax on a source machine program. -/
def transform
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    {R : Reduction P Q}
    {JP : MachineAdversaryInterface.{u, a, b} P}
    {JQ : MachineAdversaryInterface.{v, c, d} Q}
    (T : R.MachineProgramTransformation JP JQ) :
    Machine.Program → Machine.Program := T.compiler.run

/-- The polynomial majorant for a transformed runtime budget. -/
theorem budget_polynomiallyBounded
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    {R : Reduction P Q}
    {JP : MachineAdversaryInterface.{u, a, b} P}
    {JQ : MachineAdversaryInterface.{v, c, d} Q}
    (T : R.MachineProgramTransformation JP JQ)
    {q : Nat → Nat} (hq : PolynomiallyBounded q) :
    PolynomiallyBounded (T.transformBudget q) :=
  T.toSimulation.budget_polynomiallyBounded hq

theorem preservesPolynomialTime
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    {R : Reduction P Q}
    {JP : MachineAdversaryInterface.{u, a, b} P}
    {JQ : MachineAdversaryInterface.{v, c, d} Q}
    (T : R.MachineProgramTransformation JP JQ)
    {p : Machine.Program} (hp : Machine.PolynomialTime p) :
    Machine.PolynomialTime (T.transform p) :=
  T.toSimulation.preservesPolynomialTime hp

/-- The target witness is precisely the emitted machine program. -/
theorem preservesAdmissibility
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    {R : Reduction P Q}
    {JP : MachineAdversaryInterface.{u, a, b} P}
    {JQ : MachineAdversaryInterface.{v, c, d} Q}
    (T : R.MachineProgramTransformation JP JQ) :
    R.PreservesAdmissibility JP.pptClass JQ.pptClass := by
  constructor
  intro F A hA
  obtain ⟨p, q, size, hq, hHalts, hSize, hRealizes⟩ := hA
  exact ⟨T.transform p, T.transformBudget q, T.mapInputSize F size,
    T.budget_polynomiallyBounded hq, T.halts p q hHalts,
    T.size_polynomial F size hSize, T.realizes F A p q hHalts hRealizes⟩

/-- Identity on finite code, analysis budget, and input-size witness. -/
def id {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, a, b} P) :
    (Reduction.id P).MachineProgramTransformation J J where
  compiler := .identity
  transformBudget := fun q => q
  coefficient := 1
  securityDegree := 0
  sourceDegree := 1
  budget_bound := by intro q m; simp
  halts := by intro p q h input; exact h input
  realizes := by intro F A p q _hHalts h; exact h
  mapInputSize := by intro F size; exact size
  size_polynomial := by intro F size h; exact h

/-- A nontrivial, explicit compiler certificate for the identity reduction:
guarded source simulation with charged raw-input preparation and raw-output
extraction. It preserves every finite-I/O adapter's semantics under the
source's valid stopping budget, with metadata `(125, 1, 2)`. -/
def guarded {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, a, b} P) :
    (Reduction.id P).MachineProgramTransformation J J where
  compiler := .guarded
  transformBudget := GuardedCompiler.rawTraceBudget
  coefficient := 125
  securityDegree := 1
  sourceDegree := 2
  budget_bound := by
    intro q m
    simpa using GuardedCompiler.rawTraceBudget_bound q m
  halts := by
    intro p q hHalts input
    exact GuardedCompiler.rawCompile_haltsWithin p input q (hHalts input)
  realizes := by
    intro F A p q hHalts h
    change J.realizeFamily F (GuardedCompiler.rawCompile p) (GuardedCompiler.rawTraceBudget q) = A
    change J.realizeFamily F p q = A at h
    rw [← h]
    funext n
    unfold MachineAdversaryInterface.realizeFamily
    congr 1
    funext request
    unfold MachineAdversaryInterface.responseWithin
    dsimp only
    rw [GuardedCompiler.rawCompile_evalWithin p (J.machineInput n (F n) request) q (hHalts _)]
  mapInputSize := by intro F size; exact size
  size_polynomial := by intro F size h; exact h

/-- Compose code transformations and analysis budgets in reduction order.
The runtime metadata follows `c₂(c₁+1)^d₂`, `k₂+k₁d₂`, `d₁d₂`. -/
def comp {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}} {S : CryptoGoal.{w}}
    {R₁ : Reduction P Q} {R₂ : Reduction Q S}
    {JP : MachineAdversaryInterface.{u, a, b} P}
    {JQ : MachineAdversaryInterface.{v, c, d} Q}
    {JS : MachineAdversaryInterface.{w, e, f} S}
    (T₁ : R₁.MachineProgramTransformation JP JQ)
    (T₂ : R₂.MachineProgramTransformation JQ JS) :
    (R₁.comp R₂).MachineProgramTransformation JP JS where
  compiler := .comp T₁.compiler T₂.compiler
  transformBudget := fun q => T₂.transformBudget (T₁.transformBudget q)
  coefficient := T₂.coefficient * (T₁.coefficient + 1) ^ T₂.sourceDegree
  securityDegree := T₂.securityDegree + T₁.securityDegree * T₂.sourceDegree
  sourceDegree := T₁.sourceDegree * T₂.sourceDegree
  budget_bound := by
    intro q m
    let t := T₁.transformBudget q m
    let X := (m + 1) ^ T₁.securityDegree * (q m + 1) ^ T₁.sourceDegree
    have ht : t ≤ T₁.coefficient * X := by
      simpa only [t, X, mul_assoc] using T₁.budget_bound q m
    have hX : 1 ≤ X := by
      dsimp [X]
      calc
        1 = 1 * 1 := by simp
        _ ≤ (m + 1) ^ T₁.securityDegree * (q m + 1) ^ T₁.sourceDegree :=
          Nat.mul_le_mul
            (Nat.one_le_pow' T₁.securityDegree m)
            (Nat.one_le_pow' T₁.sourceDegree (q m))
    have htPlus : t + 1 ≤ (T₁.coefficient + 1) * X := by
      calc
        t + 1 ≤ T₁.coefficient * X + 1 := Nat.add_le_add_right ht 1
        _ ≤ T₁.coefficient * X + X := Nat.add_le_add_left hX _
        _ = (T₁.coefficient + 1) * X := by simp [Nat.add_mul]
    calc
      T₂.transformBudget (T₁.transformBudget q) m
          ≤ T₂.coefficient * (m + 1) ^ T₂.securityDegree *
              (t + 1) ^ T₂.sourceDegree := T₂.budget_bound _ m
      _ ≤ T₂.coefficient * (m + 1) ^ T₂.securityDegree *
          ((T₁.coefficient + 1) * X) ^ T₂.sourceDegree :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htPlus _)
      _ = (T₂.coefficient * (T₁.coefficient + 1) ^ T₂.sourceDegree) *
          (m + 1) ^ (T₂.securityDegree + T₁.securityDegree * T₂.sourceDegree) *
          (q m + 1) ^ (T₁.sourceDegree * T₂.sourceDegree) := by
        dsimp [X]
        simp only [mul_pow, pow_mul, pow_add]
        ac_rfl
  halts := by
    intro p q h input
    exact T₂.halts (T₁.transform p) (T₁.transformBudget q)
      (T₁.halts p q h) input
  realizes := by
    intro F A p q hHalts h
    exact T₂.realizes (R₁.mapFamily F) (R₁.mapAdversaryFamily F A)
      (T₁.transform p) (T₁.transformBudget q)
      (T₁.halts p q hHalts) (T₁.realizes F A p q hHalts h)
  mapInputSize := by
    intro F size
    exact T₂.mapInputSize (R₁.mapFamily F) (T₁.mapInputSize F size)
  size_polynomial := by
    intro F size h
    exact T₂.size_polynomial (R₁.mapFamily F) (T₁.mapInputSize F size)
      (T₁.size_polynomial F size h)

end MachineProgramTransformation

namespace MachineProgramSimulation

def id {P : CryptoGoal.{u}}
    (J : MachineAdversaryInterface.{u, a, b} P) :
    (Reduction.id P).MachineProgramSimulation J J :=
  (MachineProgramTransformation.id J).toSimulation

/-- Compose finite-code simulators in reduction order, without imposing a
source all-request input-size bound. The same quantitative coefficient and
degree formulas as `MachineProgramTransformation.comp` apply. -/
def comp {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}} {S : CryptoGoal.{w}}
    {R₁ : Reduction P Q} {R₂ : Reduction Q S}
    {JP : MachineAdversaryInterface.{u, a, b} P}
    {JQ : MachineAdversaryInterface.{v, c, d} Q}
    {JS : MachineAdversaryInterface.{w, e, f} S}
    (T₁ : R₁.MachineProgramSimulation JP JQ)
    (T₂ : R₂.MachineProgramSimulation JQ JS) :
    (R₁.comp R₂).MachineProgramSimulation JP JS where
  compiler := .comp T₁.compiler T₂.compiler
  transformBudget := fun q => T₂.transformBudget (T₁.transformBudget q)
  coefficient := T₂.coefficient * (T₁.coefficient + 1) ^ T₂.sourceDegree
  securityDegree := T₂.securityDegree + T₁.securityDegree * T₂.sourceDegree
  sourceDegree := T₁.sourceDegree * T₂.sourceDegree
  budget_bound := by
    intro q m
    let t := T₁.transformBudget q m
    let X := (m + 1) ^ T₁.securityDegree * (q m + 1) ^ T₁.sourceDegree
    have ht : t ≤ T₁.coefficient * X := by
      simpa only [t, X, mul_assoc] using T₁.budget_bound q m
    have hX : 1 ≤ X := by
      dsimp [X]
      calc
        1 = 1 * 1 := by simp
        _ ≤ (m + 1) ^ T₁.securityDegree * (q m + 1) ^ T₁.sourceDegree :=
          Nat.mul_le_mul
            (Nat.one_le_pow' T₁.securityDegree m)
            (Nat.one_le_pow' T₁.sourceDegree (q m))
    have htPlus : t + 1 ≤ (T₁.coefficient + 1) * X := by
      calc
        t + 1 ≤ T₁.coefficient * X + 1 := Nat.add_le_add_right ht 1
        _ ≤ T₁.coefficient * X + X := Nat.add_le_add_left hX _
        _ = (T₁.coefficient + 1) * X := by simp [Nat.add_mul]
    calc
      T₂.transformBudget (T₁.transformBudget q) m
          ≤ T₂.coefficient * (m + 1) ^ T₂.securityDegree *
              (t + 1) ^ T₂.sourceDegree := T₂.budget_bound _ m
      _ ≤ T₂.coefficient * (m + 1) ^ T₂.securityDegree *
          ((T₁.coefficient + 1) * X) ^ T₂.sourceDegree :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htPlus _)
      _ = (T₂.coefficient * (T₁.coefficient + 1) ^ T₂.sourceDegree) *
          (m + 1) ^ (T₂.securityDegree + T₁.securityDegree * T₂.sourceDegree) *
          (q m + 1) ^ (T₁.sourceDegree * T₂.sourceDegree) := by
        dsimp [X]
        simp only [mul_pow, pow_mul, pow_add]
        ac_rfl
  halts := by
    intro p q h input
    exact T₂.halts (T₁.transform p) (T₁.transformBudget q)
      (T₁.halts p q h) input
  realizes := by
    intro F A p q hHalts h
    exact T₂.realizes (R₁.mapFamily F) (R₁.mapAdversaryFamily F A)
      (T₁.transform p) (T₁.transformBudget q)
      (T₁.halts p q hHalts) (T₁.realizes F A p q hHalts h)

end MachineProgramSimulation

end Reduction
