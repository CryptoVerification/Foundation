import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyStorageExecution
import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyContractBackend

/-! Retained-data bounds for the compiled native privacy reduction, including
physical table-key generation and both actual transcripts. The external
ideal encryption game holds its own encryption key outside this controller. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyBackend
open Machine Foundation.Probability CryptoOracle
set_option backward.isDefEq.respectTransparency false

theorem initial_extent (markers input : List Bool) :
    PrivacyStorage.extent (fun _ : Bool => 1) (PrivacyMachine.initial false markers input) ≤
      markers.length + input.length + 1 := by
  cases markers <;> cases input <;> simp [PrivacyStorage.extent, PrivacyStorage.controlExtent,
    PrivacyStorage.generatorExtent, PrivacyMachine.initial, PrivateKeyGeneration.initial,
    Interactive.ControllerExtent.controlExtent, Machine.ControllerExtent.machine,
    Configuration.initial, Tape.ofBits, Tape.cells, Interactive.ControllerExtent.traceExtent] <;> omega

theorem byteOracle_bound (n : Nat) (key side : Bool) :
    ∀ state request result,
      result ∈ (PrivacyGameCodec.byteEncryptionOracle n key side state request).support →
        (fun _ : Bool => 1) result.1 ≤ (fun _ : Bool => 1) state + 0 ∧ result.2.length ≤ 2 := by
  intro state request result h
  simp only [PrivacyGameCodec.byteEncryptionOracle, Program.adaptOracle, encryptionOracle,
    OneBitEncryption.scheme, PMF.pure_map, PMF.mem_support_pure_iff] at h
  subst result
  cases state <;> simp [PrivacyGameCodec.ciphertext]

def memoryBudget (width inputLength count : Nat) : Nat :=
  PrivacyStorage.bound (2 * width + inputLength + 1 + PrivacyMachine.executionBudget width count * 4)

/-- Every possible intermediate state of the finite compiled program obeys
this bound, including native generation, signing copies and both histories. -/
theorem compiled_peak (width : Nat → Nat) (code : Interactive.Code) (r : Profile)
    (n : Nat) (encryptionKey side : Bool) (elapsed : Nat)
    (hElapsed : elapsed ≤ PrivacyMachine.executionBudget (width n) (r.count n))
    (target : PrivacyMachine.Frame Bool)
    (h : target ∈ (PrivacyMachine.eval (compiler.run code).source
      (PrivacyGameCodec.byteEncryptionOracle n encryptionKey side) elapsed
      (PrivacyMachine.initial false (List.replicate (2 * width n) true) (r.input n))).support) :
    PrivacyStorage.cells (fun _ : Bool => 1) target ≤
      memoryBudget (width n) (r.input n).length (r.count n) := by
  have hb := PrivacyStorage.peak (fun _ : Bool => 1) (compiler.run code).source
    (PrivacyGameCodec.byteEncryptionOracle n encryptionKey side) 0 2
    (byteOracle_bound n encryptionKey side)
    (PrivacyMachine.executionBudget (width n) (r.count n)) elapsed hElapsed
    (PrivacyMachine.initial false (List.replicate (2 * width n) true) (r.input n)) target h
  apply hb.trans (PrivacyStorage.bound_monotone ?_)
  have hi := initial_extent (List.replicate (2 * width n) true) (r.input n)
  simp only [List.length_replicate] at hi
  change PrivacyStorage.extent (fun _ : Bool => 1)
    (PrivacyMachine.initial false (List.replicate (2 * width n) true) (r.input n)) +
    PrivacyMachine.executionBudget (width n) (r.count n) * 4 ≤ _
  omega

/-- Polynomial initial input is explicit; source stopping alone does not
bound data that was already present before the first transition. -/
theorem memory_profile_polynomial {width inputLength count : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hInput : PolynomiallyBounded inputLength)
    (hCount : PolynomiallyBounded count) :
    PolynomiallyBounded (fun n => memoryBudget (width n) (inputLength n) (count n)) := by
  have he := ((((PolynomiallyBounded.const 2).mul hWidth).add hInput).add
    (PolynomiallyBounded.const 1)).add
    ((PrivacyMachine.execution_profile_polynomial hWidth hCount).mul (PolynomiallyBounded.const 4))
  have hb := (((PolynomiallyBounded.const 4).mul (he.mul he)).add
    ((PolynomiallyBounded.const 7).mul he)).add (PolynomiallyBounded.const 2)
  simpa only [memoryBudget, PrivacyStorage.bound, pow_two] using hb

theorem certificate_memory_polynomial (width : Nat → Nat) (F A)
    (W : (sourceObject width).Witness F A)
    (hInput : PolynomiallyBounded (fun n => (W.resources.input n).length)) :
    PolynomiallyBounded (fun n => memoryBudget (width n)
      (W.resources.input n).length (W.resources.count n)) :=
  memory_profile_polynomial W.executes.1 hInput W.executes.2.1

end Foundation.Symmetric.EncryptThenMAC.PrivacyBackend
