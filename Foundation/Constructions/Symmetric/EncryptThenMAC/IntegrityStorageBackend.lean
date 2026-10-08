import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityStorageExecution
import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityContractBackend

/-! Retained-data bounds for the existing compiled integrity reduction.
Input length is explicit: a time bound alone cannot bound preloaded input. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityBackend
open Machine Foundation.Probability CryptoOracle
set_option backward.isDefEq.respectTransparency false

theorem initial_extent (input : List Bool) :
    IntegrityStorage.extent (fun _ : Unit => 0) (IntegrityMachine.initial () input) ≤ input.length + 1 := by
  cases input <;> simp [IntegrityStorage.extent, IntegrityStorage.controlExtent,
    IntegrityMachine.initial, Interactive.ControllerExtent.controlExtent,
    Machine.ControllerExtent.machine, Configuration.initial, Tape.ofBits, Tape.cells,
    Interactive.ControllerExtent.traceExtent, IntegrityStorage.signingTrace] <;> omega

def memoryBudget (width inputLength count : Nat) : Nat :=
  IntegrityStorage.bound (inputLength + 1 + IntegrityMachine.executionBudget width count * (width + 2))

/-- Every intermediate state of the finite compiled program obeys this bound,
including native generation, failure paths, tags, copies and actual histories. -/
theorem compiled_peak (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (n : Nat) (macKey : TableMAC.Key (width n)) (elapsed : Nat)
    (hElapsed : elapsed ≤ IntegrityMachine.executionBudget (width n) (r.count n))
    (target : IntegrityMachine.Frame Unit)
    (h : target ∈ (IntegrityMachine.eval (compiler.run code).source (IntegrityGameCodec.byteSigningOracle macKey)
      elapsed (IntegrityMachine.initial () (r.input n))).support) :
    IntegrityStorage.cells (fun _ : Unit => 0) target ≤
      memoryBudget (width n) (r.input n).length (r.count n) := by
  have hOracle : ∀ state ciphertext result,
      result ∈ (IntegrityGameCodec.byteSigningOracle macKey state ciphertext).support →
        (fun _ : Unit => 0) result.1 ≤ (fun _ : Unit => 0) state + 0 ∧ result.2.length ≤ width n := by
    intro state ciphertext result hr
    exact ⟨Nat.le_refl 0, le_of_eq (IntegrityGameCodec.signing_length macKey state ciphertext result hr)⟩
  have hb := IntegrityStorage.peak (fun _ : Unit => 0) (compiler.run code).source
    (IntegrityGameCodec.byteSigningOracle macKey) 0 (width n) hOracle
    (IntegrityMachine.executionBudget (width n) (r.count n)) elapsed hElapsed
    (IntegrityMachine.initial () (r.input n)) target h
  apply hb.trans (IntegrityStorage.bound_monotone ?_)
  change IntegrityStorage.extent (fun _ : Unit => 0) (IntegrityMachine.initial () (r.input n)) +
    IntegrityMachine.executionBudget (width n) (r.count n) * (0 + width n + 2) ≤ _
  have hi := initial_extent (r.input n)
  simp only [Nat.zero_add]
  omega

/-- Polynomial input length is an additional hypothesis, not inferred from
source stopping certificates or polynomial transition count. -/
theorem memory_profile_polynomial {width inputLength count : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hInput : PolynomiallyBounded inputLength)
    (hCount : PolynomiallyBounded count) :
    PolynomiallyBounded (fun n => memoryBudget (width n) (inputLength n) (count n)) := by
  have he := (hInput.add (PolynomiallyBounded.const 1)).add
    ((IntegrityMachine.execution_profile_polynomial hWidth hCount).mul
      (hWidth.add (PolynomiallyBounded.const 2)))
  have hb := (((PolynomiallyBounded.const 4).mul (he.mul he)).add
    ((PolynomiallyBounded.const 7).mul he)).add (PolynomiallyBounded.const 2)
  simpa only [memoryBudget, IntegrityStorage.bound, pow_two] using hb


/-- The registered witness already certifies width and source transition
count. Only polynomial preloaded input length is additionally required. -/
theorem certificate_memory_polynomial (width : Nat → Nat) (F A)
    (W : (sourceObject width).Witness F A)
    (hInput : PolynomiallyBounded (fun n => (W.resources.input n).length)) :
    PolynomiallyBounded (fun n => memoryBudget (width n)
      (W.resources.input n).length (W.resources.count n)) :=
  memory_profile_polynomial W.executes.1 hInput W.executes.2.1

end Foundation.Symmetric.EncryptThenMAC.IntegrityBackend
