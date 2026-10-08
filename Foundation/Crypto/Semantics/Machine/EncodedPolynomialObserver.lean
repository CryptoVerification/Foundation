import Foundation.Crypto.Semantics.Machine.PolynomialObserver
import Foundation.Crypto.Semantics.Machine.TimedConfigurationEncoding

/-! Connect an actual polynomial observer to a supplied faithful native-state
encoding. Supported producer outcomes give explicit input, time and storage
bounds for the observer. These bounds start after the input is supplied;
a physical serialization stage must be charged separately when composed. -/
namespace Machine.PolynomialObserver
open Foundation.Probability TimedExecution
universe u
variable (O : PolynomialObserver)

/-- Semantic observer class realized by fixed polynomial-time machine code
on the given representation. This does not certify computation of E.encode. -/
def encodedClass {Value : Type u} (E : FiniteBitEncoding Value) (kernel : Value → PMF Bool) : Prop :=
  ∃ observer : PolynomialObserver, kernel = fun value => observer.observe (E.encode value)

noncomputable def observeTimed (code : Program) (result : Configuration × Nat) : PMF Bool :=
  O.observe (TimedConfigurationEncoding.encode code result)

noncomputable def costedTimed (code : Program) (result : Configuration × Nat) : PMF (Configuration × Nat) :=
  O.costed (TimedConfigurationEncoding.encode code result)

theorem observeTimed_admitted (code : Program) :
    encodedClass (TimedConfigurationEncoding.resultEncoding code) (O.observeTimed code) := ⟨O, rfl⟩

def timedBudget (code : Program) (pc cells fuel : Nat) : Nat :=
  O.budget (TimedConfigurationEncoding.bound code pc cells fuel)

def timedStorageBound (code : Program) (pc cells fuel : Nat) : Nat :=
  O.storageBound (TimedConfigurationEncoding.bound code pc cells fuel)

theorem timed_halts (code : Program) (boundary : Configuration → Bool) (fuel : Nat)
    (start : Configuration) (result : Configuration × Nat)
    (hResult : result ∈ (runToBoundary (stepPMF code) boundary fuel start).support) :
    HaltsWithin O.code (TimedConfigurationEncoding.encode code result)
      (O.timedBudget code start.pc start.tapeCells fuel) :=
  O.halts_with_input_bound _ _ (TimedConfigurationEncoding.boundary_length code boundary fuel start result hResult)

theorem timed_costed_horizon (code : Program) (boundary : Configuration → Bool) (fuel : Nat)
    (start : Configuration) (result : Configuration × Nat)
    (hResult : result ∈ (runToBoundary (stepPMF code) boundary fuel start).support) :
    runToBoundary (stepPMF O.code) Configuration.halted (O.timedBudget code start.pc start.tapeCells fuel)
      (Configuration.initial (TimedConfigurationEncoding.encode code result)) = O.costedTimed code result :=
  O.costed_horizon _ _ (O.budget_mono (TimedConfigurationEncoding.boundary_length code boundary fuel start result hResult))

theorem timed_costed_bound (code : Program) (boundary : Configuration → Bool) (fuel : Nat)
    (start : Configuration) (result : Configuration × Nat)
    (hResult : result ∈ (runToBoundary (stepPMF code) boundary fuel start).support)
    (observed : Configuration × Nat) (hObserved : observed ∈ (O.costedTimed code result).support) :
    observed.2 ≤ O.timedBudget code start.pc start.tapeCells fuel :=
  O.costed_input_bound _ _ (TimedConfigurationEncoding.boundary_length code boundary fuel start result hResult) _ hObserved

theorem timed_storage_peak (code : Program) (boundary : Configuration → Bool) (fuel : Nat)
    (start : Configuration) (result : Configuration × Nat)
    (hResult : result ∈ (runToBoundary (stepPMF code) boundary fuel start).support)
    (elapsed : Nat) (hElapsed : elapsed ≤ O.timedBudget code start.pc start.tapeCells fuel)
    (state : Configuration)
    (hState : state ∈ (eval (stepPMF O.code) elapsed
      (Configuration.initial (TimedConfigurationEncoding.encode code result))).support) :
    (StructuredCodeEncoding.completeEncoding.encode (O.code, state)).length ≤
      O.timedStorageBound code start.pc start.tapeCells fuel := by
  have hLength := TimedConfigurationEncoding.boundary_length code boundary fuel start result hResult
  have hCells : (Configuration.initial (TimedConfigurationEncoding.encode code result)).tapeCells ≤
      TimedConfigurationEncoding.bound code start.pc start.tapeCells fuel + 2 := by
    have h := PolynomialObserver.initial_cells_le (TimedConfigurationEncoding.encode code result)
    omega
  exact (StructuredCodeEncoding.peak O.code _ elapsed hElapsed _ state hState).trans
    (StructuredCodeEncoding.bound_mono _ (Nat.le_refl 0) hCells (Nat.le_refl _))

theorem timedBudget_polynomial (code : Program) {pc cells fuel : Nat → Nat}
    (hPc : PolynomiallyBounded pc) (hCells : PolynomiallyBounded cells) (hFuel : PolynomiallyBounded fuel) :
    PolynomiallyBounded (fun n => O.timedBudget code (pc n) (cells n) (fuel n)) :=
  O.budget_profile_polynomial (TimedConfigurationEncoding.bound_polynomial code hPc hCells hFuel)

theorem timedStorageBound_polynomial (code : Program) {pc cells fuel : Nat → Nat}
    (hPc : PolynomiallyBounded pc) (hCells : PolynomiallyBounded cells) (hFuel : PolynomiallyBounded fuel) :
    PolynomiallyBounded (fun n => O.timedStorageBound code (pc n) (cells n) (fuel n)) :=
  O.storage_profile_polynomial (TimedConfigurationEncoding.bound_polynomial code hPc hCells hFuel)

end Machine.PolynomialObserver
