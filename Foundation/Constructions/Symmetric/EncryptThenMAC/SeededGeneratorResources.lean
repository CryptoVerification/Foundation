import Foundation.Constructions.Symmetric.EncryptThenMAC.SeededGeneratorSecurity
import Foundation.Constructions.Symmetric.EncryptThenMAC.ProjectedGeneratedBlockMaskNativeObserverResources
import Foundation.Crypto.Semantics.Machine.NativeEncodedResources
import Foundation.Crypto.Semantics.Machine.NativeCompositionResources

/-! Actual encoded storage of the linked native generator and of its complete
unit-oracle encryption/observer experiment. Initial bounds are derived from
the marker input and public message layout; no generator scratch-space
hypothesis is supplied. Storage includes fixed code and every retained state.
This does not flatten the outer encryption controller into native code. -/
namespace Foundation.Symmetric.EncryptThenMAC.SeededGeneratorImplementation.Expander
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Examples
open Foundation.Symmetric.EncryptThenMAC ReusableResponse.Initialized
open ReusableBlockPad.NativeObserver (RuntimeState boundary publicMachine)
universe u
set_option backward.isDefEq.respectTransparency false
variable {G : Generator} (E : Expander.{u} G)

theorem projected_entry (n : Nat) : (E.projected.execution n).entry () =
    Machine.Configuration.initial (List.replicate (G.seedLength n) true) := rfl

theorem native_code (n : Nat) : (E.projected.native n).code = OneTimePad.keygen.followedBy E.code := rfl

theorem native_budget (n : Nat) : (E.projected.native n).execution.budget () =
    5 * G.seedLength n + E.cap n + 3 := E.projected_budget n

def generatorBitBound (n : Nat) : Nat := NativeEncodedResources.bound
  (OneTimePad.keygen.followedBy E.code) 0 (G.seedLength n + 2) (5 * G.seedLength n + E.cap n + 3)

theorem generator_peak (n elapsed : Nat) (hElapsed : elapsed ≤ 5 * G.seedLength n + E.cap n + 3)
    (target : Machine.Configuration)
    (h : target ∈ (TimedExecution.eval (stepPMF (OneTimePad.keygen.followedBy E.code)) elapsed
      (Machine.Configuration.initial (List.replicate (G.seedLength n) true))).support) :
    (NativeEncodedResources.completeEncoding.encode (OneTimePad.keygen.followedBy E.code, target)).length ≤
      E.generatorBitBound n := by
  have hb := (E.link n).storage_peak () elapsed
    (by
      rw [← TypedNativeComposition.Link.budget]
      change elapsed ≤ (E.assembled n).execution.budget ()
      rwa [E.assembled_budget]) target h
  unfold TypedNativeComposition.Link.bitBound at hb
  rw [← TypedNativeComposition.Link.budget] at hb
  change (NativeEncodedResources.completeEncoding.encode (OneTimePad.keygen.followedBy E.code, target)).length ≤
    NativeEncodedResources.bound (OneTimePad.keygen.followedBy E.code) 0
      (Machine.Configuration.initial (List.replicate (G.seedLength n) true)).tapeCells
      ((E.assembled n).execution.budget ()) at hb
  rw [E.assembled_budget] at hb
  have hc := Tape.cells_ofBits_le (List.replicate (G.seedLength n) true)
  simp only [List.length_replicate] at hc
  have hi : (Machine.Configuration.initial (List.replicate (G.seedLength n) true)).tapeCells ≤ G.seedLength n + 2 := by
    change (Tape.ofBits (List.replicate (G.seedLength n) true)).cells + 1 ≤ G.seedLength n + 2
    omega
  exact hb.trans (NativeEncodedResources.bound_mono _ (Nat.le_refl _) hi (Nat.le_refl _))

/-- Full retained private state is bounded using the result's actual time,
without replacing every outcome by the declared maximum duration. -/
theorem generator_costed_storage (n : Nat) (result : Machine.Configuration × Nat)
    (hResult : result ∈ ((E.assembled n).execution.costed ()).support) :
    (NativeEncodedResources.completeEncoding.encode (OneTimePad.keygen.followedBy E.code, result.1)).length ≤
      NativeEncodedResources.bound (OneTimePad.keygen.followedBy E.code) 0
        (Machine.Configuration.initial (List.replicate (G.seedLength n) true)).tapeCells result.2 :=
  (E.link n).storage_costed () result hResult

theorem generatorBitBound_polynomial (hSeed : PolynomiallyBounded G.seedLength)
    (hExpand : PolynomiallyBounded E.cap) : PolynomiallyBounded E.generatorBitBound := by
  apply NativeEncodedResources.bound_polynomial _ (PolynomiallyBounded.const 0)
    (hSeed.add (PolynomiallyBounded.const 2))
  have h := E.time_polynomial hSeed hExpand
  simpa only [projected_budget] using h

/-- Size of original caller and marker input, before any native generation. -/
def initialExtent (_ : Expander G) (n : Nat) : Nat := G.seedLength n + 2 * G.outputLength n + 3

private theorem loaded_cells (bits : List Bool) : (ResponseLoading.loaded bits).cells = bits.length + 1 := by
  cases bits with
  | nil => rfl
  | cons bit rest => simp [ResponseLoading.loaded, ResponseLoading.fromCells, Tape.cells]; omega

theorem initial_extent (n : Nat) (message : Bits (G.outputLength n)) :
    ReusableResponse.Initialized.Resources.extent (fun _ : Unit => 0)
      (ReusableBlockPad.callerFrame () [] message)
      (ProjectedGeneratedBlockMask.Resources.initial (E.projected.native n) ()) ≤ E.initialExtent n := by
  have hi := Tape.cells_ofBits_le (List.replicate (G.seedLength n) true)
  simp only [List.length_replicate] at hi
  have ho : (ResponseLoading.loaded (FlaggedBlockXor.request message.toList)).cells = 2 * G.outputLength n + 2 := by
    rw [loaded_cells, FlaggedBlockXor.request_length, Bits.length_toList]
  change max (max 0 (max (max 1 (ResponseLoading.loaded (FlaggedBlockXor.request message.toList)).cells) 0))
    (max (Tape.ofBits (List.replicate (G.seedLength n) true)).cells 1) ≤ _
  rw [ho]
  unfold initialExtent
  omega

theorem initial_address (n : Nat) (message : Bits (G.outputLength n)) :
    Encoded.maxPc (ReusableBlockPad.callerFrame () [] message)
      (ProjectedGeneratedBlockMask.Resources.initial (E.projected.native n) ()) = 0 := rfl

def encryptionBitBound (observer : Program) (observerCap : Nat → Nat) (n : Nat) : Nat :=
  ProjectedGeneratedBlockMask.NativeObserver.Resources.sourceCodeBits (OneTimePad.keygen.followedBy E.code) +
    NativeContinuation.Resources.bound observer
      (Encoded.bound (OneTimePad.keygen.followedBy E.code) FlaggedBlockXor.code ReusableBlockPad.code
        0 (E.initialExtent n) (E.encryptionHorizon observerCap n) 0 0)
      (ReusableInitializationStorage.bound (E.initialExtent n) (E.encryptionHorizon observerCap n) 4 3 0 + 2)
      (E.encryptionHorizon observerCap n)

private theorem public_bound_mono {first next : Nat} (h : first ≤ next) (horizon : Nat) :
    ReusableInitializationStorage.bound first horizon 4 3 0 + 2 ≤
      ReusableInitializationStorage.bound next horizon 4 3 0 + 2 := by
  have he := Nat.add_le_add_right h (horizon * (4 + 1))
  have hq := Nat.pow_le_pow_left he 2
  simp only [ReusableInitializationStorage.bound]
  omega

/-- Every phase, including retained generation state during observation.
No security or observer-termination premise is needed. -/
theorem encryption_peak (n : Nat) (message : Bits (G.outputLength n)) (observer : Program)
    (observerCap : Nat → Nat) (elapsed : Nat) (hElapsed : elapsed ≤ E.encryptionHorizon observerCap n)
    (target : NativeContinuation.Control (RuntimeState Unit))
    (hTarget : target ∈ (TimedExecution.eval
      (NativeContinuation.step
        (ProjectedGeneratedBlockMask.step (E.projected.native n) ReusableBlockPadEncodedBackend.unitOracle () [] message)
        boundary publicMachine observer) elapsed
      (.producing (ProjectedGeneratedBlockMask.Resources.initial (E.projected.native n) ()))).support) :
    ((ProjectedGeneratedBlockMask.NativeObserver.Resources.completeEncoding () [] message FiniteBitEncoding.unit).encode
      (OneTimePad.keygen.followedBy E.code, PrivateKeyCopy.code, FlaggedBlockXor.code, ReusableBlockPad.code,
        (observer, target))).length ≤ E.encryptionBitBound observer observerCap n := by
  have he := E.initial_extent n message
  have hp := ProjectedGeneratedBlockMask.NativeObserver.Resources.peak (E.projected.native n) ()
    ReusableBlockPadEncodedBackend.unitOracle () [] message FiniteBitEncoding.unit
    (fun _ => 0) (fun _ => Nat.le_refl 0) 0 0
    (by
      intro state request result hr
      rw [ReusableBlockPadEncodedBackend.unitOracle, PMF.mem_support_pure_iff] at hr
      subst result
      simp)
    observer (observerCap n) elapsed (by simpa only [ProjectedGeneratedBlockMask.NativeObserver.Resources.horizon, encryptionHorizon, native_budget] using hElapsed) target hTarget
  have hs := Encoded.bound_mono_initial (OneTimePad.keygen.followedBy E.code) FlaggedBlockXor.code ReusableBlockPad.code
    (firstPc := 0) (nextPc := 0) (Nat.le_refl _) he (E.encryptionHorizon observerCap n) 0 0
  have ht := public_bound_mono he (E.encryptionHorizon observerCap n)
  have hb := NativeContinuation.Resources.bound_mono observer hs ht (E.encryptionHorizon observerCap n)
  simp only [ProjectedGeneratedBlockMask.NativeObserver.Resources.bitBound,
    ProjectedGeneratedBlockMask.NativeObserver.Resources.sourceBound,
    ProjectedGeneratedBlockMask.NativeObserver.Resources.publicTapeBound,
    ProjectedGeneratedBlockMask.NativeObserver.Resources.horizon, native_budget, initial_address, native_code] at hp
  have hBound := Nat.add_le_add_left hb
    (ProjectedGeneratedBlockMask.NativeObserver.Resources.sourceCodeBits (OneTimePad.keygen.followedBy E.code))
  apply hp.trans
  simpa only [encryptionBitBound, encryptionHorizon] using hBound

/-- All supplied profiles concern seed/output lengths and genuine native
execution times; no separate initial-layout or scratch-space profile is needed. -/
theorem encryptionBitBound_polynomial (observer : Program) (observerCap : Nat → Nat)
    (hSeed : PolynomiallyBounded G.seedLength) (hExpand : PolynomiallyBounded E.cap)
    (hWidth : PolynomiallyBounded G.outputLength) (hObserver : PolynomiallyBounded observerCap) :
    PolynomiallyBounded (E.encryptionBitBound observer observerCap) := by
  have hExtent := ((hSeed.add ((PolynomiallyBounded.const 2).mul hWidth)).add (PolynomiallyBounded.const 3))
  have ht := E.encryption_time_polynomial observerCap hSeed hExpand hWidth hObserver
  have hs := Encoded.bound_polynomial (OneTimePad.keygen.followedBy E.code) FlaggedBlockXor.code ReusableBlockPad.code
    (PolynomiallyBounded.const 0) hExtent ht (PolynomiallyBounded.const 0) (PolynomiallyBounded.const 0)
  have hp := (ReusableInitializationStorage.bound_polynomial hExtent ht (PolynomiallyBounded.const 4) 3 0).add
    (PolynomiallyBounded.const 2)
  exact (PolynomiallyBounded.const (ProjectedGeneratedBlockMask.NativeObserver.Resources.sourceCodeBits
    (OneTimePad.keygen.followedBy E.code))).add (NativeContinuation.Resources.bound_polynomial observer hs hp ht)

/-- Native generation, full encryption experiment and both reductions have
polynomial resource profiles under the same physical length/time conditions. -/
theorem resource_profiles (observer : Program) (observerCap : Nat → Nat)
    (hSeed : PolynomiallyBounded G.seedLength) (hExpand : PolynomiallyBounded E.cap)
    (hWidth : PolynomiallyBounded G.outputLength) (hObserver : PolynomiallyBounded observerCap) :
    PolynomiallyBounded E.generatorBitBound ∧
    PolynomiallyBounded (E.encryptionHorizon observerCap) ∧
    PolynomiallyBounded (E.encryptionBitBound observer observerCap) ∧
    PolynomiallyBounded (NativeMaskReductionSpaceBackend.bitCap G observer observerCap) :=
  ⟨E.generatorBitBound_polynomial hSeed hExpand,
    E.encryption_time_polynomial observerCap hSeed hExpand hWidth hObserver,
    E.encryptionBitBound_polynomial observer observerCap hSeed hExpand hWidth hObserver,
    NativeMaskReductionSpaceBackend.bitCap_polynomial G observer observerCap hWidth hObserver⟩

end Foundation.Symmetric.EncryptThenMAC.SeededGeneratorImplementation.Expander
