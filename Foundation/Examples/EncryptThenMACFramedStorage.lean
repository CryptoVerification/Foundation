import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyStorageExecution
import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityStorageExecution
import Foundation.Crypto.Semantics.FramingResourceEnvelope

/-! Both native reduction controllers reuse the same nonlinear saved-frame
resource rule. Saved caller data is explicitly counted at the entry; creating
or copying the saved frame is not asserted to take zero transitions. -/
namespace Foundation.EncryptThenMACFramedStorageExamples
open Foundation.Probability Foundation.Symmetric.EncryptThenMAC
universe u v
variable {State : Type u} {Saved : Type v}

theorem privacy (stateSize : State → Nat) (savedSize : Saved → Nat)
    (code : PrivacyMachine.Source.Code) (oracle : CryptoOracle.Interactive.BitOracle State)
    (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start : PrivacyMachine.Frame State) (saved : Saved) (target : PrivacyMachine.Frame State × Saved)
    (h : target ∈ (TimedExecution.eval (TimedExecution.framedStep (PrivacyMachine.step code oracle))
      elapsed (start, saved)).support) :
    target.2 = saved ∧
      PrivacyStorage.cells stateSize target.1 + savedSize target.2 ≤
        PrivacyStorage.bound (PrivacyStorage.extent stateSize start + savedSize saved +
          horizon * (stateIncrement + responseCap + 2)) +
            (PrivacyStorage.extent stateSize start + savedSize saved +
              horizon * (stateIncrement + responseCap + 2)) := by
  refine ⟨TimedExecution.framed_saved (PrivacyMachine.step code oracle) elapsed start saved target h, ?_⟩
  exact (PrivacyStorage.envelope stateSize code oracle stateIncrement responseCap hOracle).framed_peak
    savedSize horizon elapsed hElapsed (start, saved) target h

theorem integrity (stateSize : State → Nat) (savedSize : Saved → Nat)
    (code : IntegrityMachine.SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (stateIncrement tagCap : Nat)
    (hOracle : ∀ state ciphertext result, result ∈ (oracle state ciphertext).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ tagCap)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start : IntegrityMachine.Frame State) (saved : Saved) (target : IntegrityMachine.Frame State × Saved)
    (h : target ∈ (TimedExecution.eval (TimedExecution.framedStep (IntegrityMachine.step code oracle))
      elapsed (start, saved)).support) :
    target.2 = saved ∧
      IntegrityStorage.cells stateSize target.1 + savedSize target.2 ≤
        IntegrityStorage.bound (IntegrityStorage.extent stateSize start + savedSize saved +
          horizon * (stateIncrement + tagCap + 2)) +
            (IntegrityStorage.extent stateSize start + savedSize saved +
              horizon * (stateIncrement + tagCap + 2)) := by
  refine ⟨TimedExecution.framed_saved (IntegrityMachine.step code oracle) elapsed start saved target h, ?_⟩
  exact (IntegrityStorage.envelope stateSize code oracle stateIncrement tagCap hOracle).framed_peak
    savedSize horizon elapsed hElapsed (start, saved) target h

end Foundation.EncryptThenMACFramedStorageExamples
