import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityEncoding
import Foundation.Crypto.Semantics.Oracle.SourceActionAddresses

/-! Real growth of all scalar fields: native/source addresses, preparation
phases and header phases. Arbitrary initial phases are counted explicitly. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityEncoding
open Machine Foundation.Probability CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u}

def maxScalar : IntegrityMachine.Control → Nat
  | .initializing s g => max (CryptoOracle.Interactive.ConfigurationEncoding.pc s) g.pc
  | .source _ _ s => CryptoOracle.Interactive.ConfigurationEncoding.pc s
  | .encrypting _ _ c _ p => max c.pc (preparationScalar p)
  | .header _ c _ _ _ phase _ => max c.pc phase
  | .failure _ c _ | .copying _ c _ _ _ | .advancing _ c _ _ _ |
      .rewinding _ c _ _ | .collecting _ c _ _ _ | .reversing _ c _ _ _ => c.pc

theorem scalar_le_twice (c : IntegrityMachine.Control) : scalar c ≤ 2 * maxScalar c := by
  cases c <;> simp only [scalar, maxScalar] <;> omega

private noncomputable def runAction (oracle : State → Bool → PMF (State × List Bool))
    (state : State) : IntegrityMachine.Action State → PMF (IntegrityMachine.Frame State)
  | .deterministic next => PMF.pure next
  | .random zero one => sampleBit.map (fun bit => if bit then one else zero)
  | .sign ciphertext resume => (oracle state ciphertext).map resume

private theorem native_action_run (oracle : State → Bool → PMF (State × List Bool))
    (state : State) (program : Program) (machine : Machine.Configuration)
    (embed : Machine.Configuration → IntegrityMachine.Frame State) :
    runAction oracle state (IntegrityMachine.nativeAction program machine embed) =
      (stepPMF program machine).map embed := by
  cases hn : Machine.next program machine with
  | none => simp [runAction, IntegrityMachine.nativeAction, stepPMF, hn, PMF.pure_map]
  | some result =>
      cases result with
      | inl target => simp [runAction, IntegrityMachine.nativeAction, stepPMF, hn, PMF.pure_map]
      | inr pair =>
          simp only [runAction, IntegrityMachine.nativeAction, stepPMF, hn, PMF.map_comp]
          congr 1
          funext bit
          cases bit <;> rfl

private theorem native_action_bound (oracle : State → Bool → PMF (State × List Bool)) (state : State)
    (program : Program) (machine : Machine.Configuration)
    (embed : Machine.Configuration → IntegrityMachine.Frame State) (cap : Nat)
    (hEmbed : ∀ next, next.pc ≤ machine.pc + (program.addressCap + 1) → maxScalar (embed next).control ≤ cap)
    (target : IntegrityMachine.Frame State)
    (h : target ∈ (runAction oracle state (IntegrityMachine.nativeAction program machine embed)).support) :
    maxScalar target.control ≤ cap := by
  rw [native_action_run, PMF.mem_support_map_iff] at h
  obtain ⟨next, hn, he⟩ := h
  subst target
  exact hEmbed next (Machine.pc_le_of_support program machine next hn)

theorem prepare_scalar (used key message : Bool) (phase : Nat) (tape : Tape) :
    preparationScalar (IntegrityPreparation.prepareNext used key message phase tape) ≤ phase + 1 := by
  unfold IntegrityPreparation.prepareNext
  split <;> simp only [preparationScalar] <;> omega

def increment (code : IntegrityMachine.SourceCode) : Nat :=
  OneBitEncryption.Native.keygenCode.addressCap + OneBitEncryption.Native.encryptionCode.addressCap +
    EncodedStorage.addressCap code + 1

theorem max_scalar_step (code : IntegrityMachine.SourceCode)
    (oracle : State → Bool → PMF (State × List Bool)) (start target : IntegrityMachine.Frame State)
    (h : target ∈ (IntegrityMachine.step code oracle start).support) :
    maxScalar target.control ≤ maxScalar start.control + increment code := by
  rcases start with ⟨state, c, sourceTrace, tags⟩
  cases c with
  | initializing s g =>
      by_cases hh : g.halted = true
      · simp [IntegrityMachine.step, IntegrityMachine.transition, hh] at h
        subst target
        simp only [maxScalar, increment]
        omega
      · simp only [IntegrityMachine.step, IntegrityMachine.transition, hh, Bool.false_eq_true, ↓reduceIte] at h
        apply native_action_bound oracle state _ g _ _ ?_ target h
        intro next hp
        simp only [maxScalar, increment]
        omega
  | source key used s =>
      by_cases hh : Reification.terminal s = true
      · simp [IntegrityMachine.step, IntegrityMachine.transition, hh] at h
        subst target
        omega
      · have hf : Reification.terminal s = false := by simpa using hh
        cases ha : Reification.action code s with
        | deterministic next =>
            have hp := EncodedStorage.deterministic_action_pc code s next hf ha
            simp [IntegrityMachine.step, IntegrityMachine.transition, hf, ha] at h
            subst target
            simp only [maxScalar, increment]
            omega
        | random zero one =>
            simp only [IntegrityMachine.step, IntegrityMachine.transition, hf, Bool.false_eq_true,
              ↓reduceIte, ha, PMF.mem_support_map_iff] at h
            obtain ⟨bit, _, he⟩ := h
            subst target
            have hp := EncodedStorage.random_action_pc code s zero one hf ha bit
            cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte, maxScalar, increment] at * <;> omega
        | oracleCall c request =>
            have hp := EncodedStorage.oracle_action_pc code s c request hf ha
            simp [IntegrityMachine.step, IntegrityMachine.transition, hf, ha] at h
            subst target
            simp only [maxScalar, preparationScalar, IntegrityPreparation.initial, increment]
            omega
  | encrypting key used c request p =>
      cases hr : IntegrityPreparation.ready p with
      | some result =>
          rcases result with ⟨newUsed, ciphertext⟩
          cases ciphertext with
          | none =>
              simp [IntegrityMachine.step, IntegrityMachine.transition, hr] at h
              subst target
              simp only [maxScalar, increment]
              omega
          | some ciphertext =>
              simp only [IntegrityMachine.step, IntegrityMachine.transition, hr, PMF.mem_support_map_iff] at h
              obtain ⟨answer, _, he⟩ := h
              subst target
              simp only [maxScalar, increment]
              omega
      | none =>
          cases p with
          | preparing phase t =>
              have hp := prepare_scalar used key (request.head?.getD false) phase t
              simp only [preparationScalar] at hp
              simp [IntegrityMachine.step, IntegrityMachine.transition, hr] at h
              subst target
              simp only [maxScalar, preparationScalar, increment]
              omega
          | encrypting machine =>
              simp only [IntegrityMachine.step, IntegrityMachine.transition, hr] at h
              apply native_action_bound oracle state _ machine _ _ ?_ target h
              intro next hp
              simp only [maxScalar, preparationScalar, increment]
              omega
  | failure key c request =>
      simp [IntegrityMachine.step, IntegrityMachine.transition] at h
      subst target
      simp [maxScalar]
  | header key c request ciphertext tag phase t =>
      simp only [IntegrityMachine.step, IntegrityMachine.transition] at h
      split at h <;> simp only [PMF.mem_support_pure_iff] at h <;> subst target <;>
        simp only [maxScalar, increment] <;> omega
  | copying key c request rest t =>
      cases rest <;> simp [IntegrityMachine.step, IntegrityMachine.transition] at h <;> subst target <;> simp [maxScalar]
  | advancing key c request rest t =>
      simp [IntegrityMachine.step, IntegrityMachine.transition] at h
      subst target
      simp [maxScalar]
  | rewinding key c request t =>
      cases ht : t.left <;> simp [IntegrityMachine.step, IntegrityMachine.transition, ht] at h <;>
        subst target <;> simp [maxScalar]
  | collecting key c request t acc =>
      cases ht : t.current <;> simp [IntegrityMachine.step, IntegrityMachine.transition, ht] at h <;>
        subst target <;> simp [maxScalar]
  | reversing key c request rest response =>
      cases rest <;> simp [IntegrityMachine.step, IntegrityMachine.transition] at h <;> subst target <;>
        simp [maxScalar, CryptoOracle.Interactive.ConfigurationEncoding.pc]

end Foundation.Symmetric.EncryptThenMAC.IntegrityEncoding
