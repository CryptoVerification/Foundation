import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyEncoding
import Foundation.Crypto.Semantics.Oracle.SourceActionAddresses

/-! Actual address growth of the full privacy reduction, including saved
source addresses and both native authentication subprograms. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyEncoding
open Machine Foundation.Probability CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false

def maxPc : PrivacyMachine.Control → Nat
  | .initializing s g => max (CryptoOracle.Interactive.ConfigurationEncoding.pc s) (generatorPc g)
  | .source _ s => CryptoOracle.Interactive.ConfigurationEncoding.pc s
  | .responding c _ r => max c.pc (responderPc r)
  | .rewinding _ c _ _ | .collecting _ c _ _ _ | .reversing _ c _ _ _ => c.pc

theorem pc_le_twice (c : PrivacyMachine.Control) : pc c ≤ 2 * maxPc c := by
  cases c <;> simp only [pc, maxPc] <;> omega

theorem generator_pc_step (start target : PrivateKeyGeneration.Control)
    (h : target ∈ (PrivateKeyGeneration.step start).support) :
    generatorPc target ≤ generatorPc start + (OneTimePad.Native.keygenCode.addressCap + 1) := by
  cases start with
  | generating c =>
      by_cases hh : c.halted = true
      · simp [PrivateKeyGeneration.step, hh] at h
        subst target
        simp [generatorPc]
      · simp only [PrivateKeyGeneration.step, hh, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
        obtain ⟨next, hn, he⟩ := h
        subst target
        exact Machine.pc_le_of_support _ c next hn
  | rewinding t =>
      cases ht : t.left <;> simp [PrivateKeyGeneration.step, ht] at h <;> subst target <;> simp [generatorPc]
  | ready t => simp [PrivateKeyGeneration.step] at h; subst target; omega

theorem responder_pc_step (start target : ResponseHandoff.Control)
    (h : target ∈ (ResponseHandoff.step start).support) :
    responderPc target ≤ responderPc start + (PrivateKeyCopy.code.addressCap + AuthenticateResponse.code.addressCap + 1) := by
  cases start with
  | headerWriting key rest buffer =>
      cases rest <;> simp [ResponseHandoff.step] at h <;> subst target <;> simp [responderPc]
  | headerAdvancing key rest buffer =>
      simp [ResponseHandoff.step] at h
      subst target
      simp [responderPc]
  | copying c =>
      by_cases hh : c.halted = true
      · simp [ResponseHandoff.step, hh] at h
        subst target
        simp [responderPc]
      · simp only [ResponseHandoff.step, hh, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at h
        obtain ⟨next, hn, he⟩ := h
        subst target
        have hp := Machine.pc_le_of_support _ c next hn
        simp only [responderPc]
        omega
  | rewinding key buffer =>
      cases ht : buffer.left <;> simp [ResponseHandoff.step, ht] at h <;> subst target <;> simp [responderPc]
  | authenticating key c =>
      simp only [ResponseHandoff.step, PMF.mem_support_map_iff] at h
      obtain ⟨next, hn, he⟩ := h
      subst target
      have hp := Machine.pc_le_of_support _ c next hn
      simp only [responderPc]
      omega

def increment (code : PrivacyMachine.Source.Code) : Nat :=
  OneTimePad.Native.keygenCode.addressCap + PrivateKeyCopy.code.addressCap +
    AuthenticateResponse.code.addressCap + EncodedStorage.addressCap code + 1

theorem max_pc_step {State : Type u} (code : PrivacyMachine.Source.Code) (oracle : BitOracle State)
    (start target : PrivacyMachine.Frame State) (h : target ∈ (PrivacyMachine.step code oracle start).support) :
    maxPc target.control ≤ maxPc start.control + increment code := by
  rcases start with ⟨state, c, sourceTrace, externalTrace⟩
  cases c with
  | initializing s g =>
      cases hr : PrivateKeyGeneration.readyStore g with
      | some key =>
          simp [PrivacyMachine.step, hr] at h
          subst target
          simp only [maxPc, increment]
          omega
      | none =>
          simp only [PrivacyMachine.step, hr, PMF.mem_support_map_iff] at h
          obtain ⟨next, hn, he⟩ := h
          subst target
          have hp := generator_pc_step g next hn
          simp only [maxPc, increment]
          omega
  | source key s =>
      by_cases hh : Reification.terminal s = true
      · simp [PrivacyMachine.step, hh] at h
        subst target
        omega
      · have hf : Reification.terminal s = false := by simpa using hh
        cases ha : Reification.action code s with
        | deterministic next =>
            have hp := EncodedStorage.deterministic_action_pc code s next hf ha
            simp [PrivacyMachine.step, hf, ha] at h
            subst target
            simp only [maxPc, increment]
            omega
        | random zero one =>
            simp only [PrivacyMachine.step, hf, Bool.false_eq_true, ↓reduceIte, ha, PMF.mem_support_map_iff] at h
            obtain ⟨bit, _, he⟩ := h
            subst target
            have hp := EncodedStorage.random_action_pc code s zero one hf ha bit
            simp only [maxPc, increment]
            omega
        | oracleCall c request =>
            simp only [PrivacyMachine.step, hf, Bool.false_eq_true, ↓reduceIte, ha, PMF.mem_support_map_iff] at h
            obtain ⟨answer, _, he⟩ := h
            subst target
            have hp := EncodedStorage.oracle_action_pc code s c request hf ha
            simp only [maxPc, responderPc, increment]
            omega
  | responding c request r =>
      cases hr : PrivacyMachine.responseOutput r with
      | some pair =>
          rcases pair with ⟨key, output⟩
          simp [PrivacyMachine.step, hr] at h
          subst target
          simp only [maxPc, increment]
          omega
      | none =>
          simp only [PrivacyMachine.step, hr, PMF.mem_support_map_iff] at h
          obtain ⟨next, hn, he⟩ := h
          subst target
          have hp := responder_pc_step r next hn
          simp only [maxPc, increment]
          omega
  | rewinding key c request t =>
      cases ht : t.left <;> simp [PrivacyMachine.step, ht] at h <;> subst target <;> simp [maxPc]
  | collecting key c request t acc =>
      cases ht : t.current <;> simp [PrivacyMachine.step, ht] at h <;> subst target <;> simp [maxPc]
  | reversing key c request rest response =>
      cases rest <;> simp [PrivacyMachine.step] at h <;> subst target <;>
        simp [maxPc, CryptoOracle.Interactive.ConfigurationEncoding.pc]

end Foundation.Symmetric.EncryptThenMAC.PrivacyEncoding
