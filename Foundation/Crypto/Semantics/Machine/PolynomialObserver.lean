import Foundation.Crypto.Semantics.Machine.PPT
import Foundation.Crypto.Semantics.Machine.StructuredCodeEncoding
import Foundation.Crypto.Semantics.BoundaryStability
import Foundation.Crypto.Semantics.Machine.Procedure

/-! Fixed-code polynomial observers on supplied bitstrings.
A monomial certificate bounds all inputs and every random branch. The
observed bit is the output head cell at actual halt; blanks read false.
Input serialization is outside this machine contract and is not free code.
No arbitrary mathematical decoder is hidden in the output convention. -/
namespace Machine
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

structure PolynomialObserver where
  code : Program
  coefficient : Nat
  degree : Nat
  halts : ∀ input : List Bool, HaltsWithin code input (coefficient * (input.length + 1) ^ degree)

namespace PolynomialObserver
variable (O : PolynomialObserver)

def budget (size : Nat) : Nat := O.coefficient * (size + 1) ^ O.degree

theorem budget_mono {first second : Nat} (h : first ≤ second) : O.budget first ≤ O.budget second :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem budget_polynomial : PolynomiallyBounded O.budget :=
  (PolynomiallyBounded.const O.coefficient).mul
    ((PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)).pow O.degree)

theorem polynomialTime : PolynomialTime O.code := ⟨O.budget, O.budget_polynomial, O.halts⟩

/-- This certificate covers exactly the library's fixed-code polynomial-time programs. -/
theorem exists_iff_polynomialTime (code : Program) :
    (∃ observer : PolynomialObserver, observer.code = code) ↔ PolynomialTime code := by
  constructor
  · rintro ⟨observer, rfl⟩
    exact observer.polynomialTime
  · rintro ⟨q, hq, hHalts⟩
    obtain ⟨c, k, hGlobal⟩ := MachineAdversaryInterface.global_monomial_of_polynomiallyBounded hq
    exact ⟨⟨code, c, k, fun input => (hHalts input).mono (hGlobal input.length)⟩, rfl⟩

noncomputable def costed (input : List Bool) : PMF (Configuration × Nat) :=
  runToBoundary (stepPMF O.code) Configuration.halted (O.budget input.length) (Configuration.initial input)

/-- One designated output cell is read; there is no arbitrary postprocessor. -/
noncomputable def observe (input : List Bool) : PMF Bool :=
  (O.costed input).map (fun result => result.1.outputTape.current.getD false)

theorem costed_halted (input : List Bool) (result : Configuration × Nat)
    (hResult : result ∈ (O.costed input).support) : result.1.halted = true := by
  apply runToBoundary_completes (stepPMF O.code) Configuration.halted _ _ _ result hResult
  intro state hState
  rw [timed_eval_eq] at hState
  exact O.halts input state ((mem_support_evalConfigWithin_iff _ _ _ _).mp hState)

theorem costed_bounded (input : List Bool) (result : Configuration × Nat)
    (hResult : result ∈ (O.costed input).support) : result.2 ≤ O.budget input.length :=
  runToBoundary_bounded _ _ _ _ result hResult

/-- Extra analysis fuel never appears in the actual-time observation. -/
theorem costed_horizon (input : List Bool) (horizon : Nat) (hTime : O.budget input.length ≤ horizon) :
    runToBoundary (stepPMF O.code) Configuration.halted horizon (Configuration.initial input) = O.costed input := by
  exact runToBoundary_fuel_stable _ _ _ _ _ hTime (O.costed_halted input)

/-- Two halting certificates for the same code have the same full state/time law. -/
theorem costed_eq_of_code_eq (other : PolynomialObserver) (sameCode : O.code = other.code) (input : List Bool) :
    O.costed input = other.costed input := by
  have hFirst := O.costed_horizon input (max (O.budget input.length) (other.budget input.length)) (le_max_left _ _)
  have hSecond := other.costed_horizon input (max (O.budget input.length) (other.budget input.length)) (le_max_right _ _)
  rw [sameCode] at hFirst
  exact hFirst.symm.trans hSecond

def storageBound (size : Nat) : Nat :=
  StructuredCodeEncoding.bound O.code 0 (size + 2) (O.budget size)

theorem storageBound_mono {first second : Nat} (h : first ≤ second) :
    O.storageBound first ≤ O.storageBound second :=
  StructuredCodeEncoding.bound_mono _ (Nat.le_refl 0) (by omega) (O.budget_mono h)

theorem halts_with_input_bound (input : List Bool) (size : Nat) (hSize : input.length ≤ size) :
    HaltsWithin O.code input (O.budget size) := (O.halts input).mono (O.budget_mono hSize)

theorem storage_polynomial : PolynomiallyBounded O.storageBound :=
  StructuredCodeEncoding.bound_polynomial _ (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2)) O.budget_polynomial

theorem initial_cells_le (input : List Bool) : (Configuration.initial input).tapeCells ≤ input.length + 2 := by
  cases input <;> simp [Configuration.initial, Tape.ofBits, Configuration.tapeCells, Tape.cells]
  omega

theorem storage_peak (input : List Bool) (elapsed : Nat) (hElapsed : elapsed ≤ O.budget input.length)
    (state : Configuration)
    (hState : state ∈ (eval (stepPMF O.code) elapsed (Configuration.initial input)).support) :
    (StructuredCodeEncoding.completeEncoding.encode (O.code, state)).length ≤ O.storageBound input.length :=
  (StructuredCodeEncoding.peak O.code _ elapsed hElapsed _ state hState).trans
    (StructuredCodeEncoding.bound_mono _ (Nat.le_refl 0) (initial_cells_le input) (Nat.le_refl _))

/-- A public input-length bound gives a security-parameter runtime bound. -/
theorem costed_input_bound (input : List Bool) (size : Nat) (hSize : input.length ≤ size)
    (result : Configuration × Nat) (hResult : result ∈ (O.costed input).support) : result.2 ≤ O.budget size :=
  (O.costed_bounded input result hResult).trans (O.budget_mono hSize)

theorem budget_profile_polynomial {size : Nat → Nat} (hSize : PolynomiallyBounded size) :
    PolynomiallyBounded (fun n => O.budget (size n)) :=
  (PolynomiallyBounded.const O.coefficient).mul ((hSize.add (PolynomiallyBounded.const 1)).pow O.degree)

theorem storage_profile_polynomial {size : Nat → Nat} (hSize : PolynomiallyBounded size) :
    PolynomiallyBounded (fun n => O.storageBound (size n)) :=
  StructuredCodeEncoding.bound_polynomial _ (PolynomiallyBounded.const 0)
    (hSize.add (PolynomiallyBounded.const 2)) (O.budget_profile_polynomial hSize)

end PolynomialObserver
end Machine
