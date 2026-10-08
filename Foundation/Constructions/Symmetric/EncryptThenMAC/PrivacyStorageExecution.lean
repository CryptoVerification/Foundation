import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacyStorage
import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacySourceExecution
import Foundation.Crypto.Semantics.Oracle.SourceActionExtent

/-! Every real privacy-controller transition respects the resource envelope.
The private sampler and authentication handler use the existing generic
native-instruction bound; public source actions reuse the common rules. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyStorage
open Machine Foundation.Probability CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {State : Type u}

theorem generator_step (start target : PrivateKeyGeneration.Control)
    (h : target ∈ (PrivateKeyGeneration.step start).support) :
    generatorExtent target ≤ generatorExtent start + 1 := by
  cases start with
  | generating machine =>
      by_cases hh : machine.halted = true
      · simp [PrivateKeyGeneration.step, hh] at h
        subst target
        simp only [generatorExtent, Machine.ControllerExtent.machine]
        omega
      · simp only [PrivateKeyGeneration.step, hh, Bool.false_eq_true, ↓reduceIte,
          PMF.mem_support_map_iff] at h
        obtain ⟨native, hn, he⟩ := h
        subst target
        exact Machine.ControllerExtent.native_bound OneTimePad.Native.keygenCode machine native hn
  | rewinding tape =>
      have hl := Tape.cells_moveLeft_le tape
      cases ht : tape.left <;> simp [PrivateKeyGeneration.step, ht] at h <;> subst target <;>
        simp only [generatorExtent] <;> omega
  | ready tape => simp [PrivateKeyGeneration.step] at h; subst target; omega

theorem generator_ready (generator : PrivateKeyGeneration.Control) (key : Tape)
    (h : PrivateKeyGeneration.readyStore generator = some key) : key.cells ≤ generatorExtent generator := by
  cases generator <;> simp only [PrivateKeyGeneration.readyStore, Option.some.injEq,
    reduceCtorEq] at h
  subst key
  exact Nat.le_refl _

theorem responder_step (start target : ResponseHandoff.Control)
    (h : target ∈ (ResponseHandoff.step start).support) :
    responderExtent target ≤ responderExtent start + 1 := by
  cases start with
  | headerWriting key remaining buffer =>
      cases remaining <;> simp [ResponseHandoff.step] at h <;> subst target <;>
        simp only [responderExtent, Machine.ControllerExtent.machine, Tape.cells_write,
          List.length_cons] <;> omega
  | headerAdvancing key remaining buffer =>
      have hb := Tape.cells_moveRight_le buffer
      simp [ResponseHandoff.step] at h
      subst target
      simp only [responderExtent]
      omega
  | copying machine =>
      by_cases hh : machine.halted = true
      · simp [ResponseHandoff.step, hh] at h
        subst target
        exact le_add_right (Nat.le_refl _)
      · simp only [ResponseHandoff.step, hh, Bool.false_eq_true, ↓reduceIte,
          PMF.mem_support_map_iff] at h
        obtain ⟨native, hn, he⟩ := h
        subst target
        exact Machine.ControllerExtent.native_bound PrivateKeyCopy.code machine native hn
  | rewinding key buffer =>
      have hb := Tape.cells_moveLeft_le buffer
      cases hl : buffer.left <;> simp [ResponseHandoff.step, hl] at h <;> subst target <;>
        simp only [responderExtent, Machine.ControllerExtent.machine]
      · change max key.cells (max buffer.cells 1) ≤ max key.cells buffer.cells + 1
        omega
      · omega
  | authenticating key machine =>
      simp only [ResponseHandoff.step, PMF.mem_support_map_iff] at h
      obtain ⟨native, hn, he⟩ := h
      subst target
      have hb := Machine.ControllerExtent.native_bound AuthenticateResponse.code machine native hn
      simp only [responderExtent]
      omega

theorem responder_ready (responder : ResponseHandoff.Control) (key output : Tape)
    (h : PrivacyMachine.responseOutput responder = some (key, output)) :
    key.cells ≤ responderExtent responder ∧ output.cells ≤ responderExtent responder := by
  cases responder <;> simp only [PrivacyMachine.responseOutput, reduceCtorEq] at h
  rename_i retained machine
  split at h
  · cases h
    simp only [responderExtent, Machine.ControllerExtent.machine]
    omega
  · contradiction

private theorem header_length (ciphertext : Option Bool) : (ResponseHandoff.header ciphertext).length ≤ 2 := by
  cases ciphertext <;> simp [ResponseHandoff.header]

theorem step_extent (stateSize : State → Nat) (code : PrivacyMachine.Source.Code)
    (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (start target : PrivacyMachine.Frame State)
    (h : target ∈ (PrivacyMachine.step code oracle start).support) :
    extent stateSize target ≤ extent stateSize start + stateIncrement + responseCap + 2 := by
  rcases start with ⟨state, control, sourceTrace, externalTrace⟩
  have hs := ControllerExtent.trace_length sourceTrace
  have ht := ControllerExtent.trace_length externalTrace
  cases control with
  | initializing source generator =>
      cases hr : PrivateKeyGeneration.readyStore generator with
      | some key =>
          have hg := generator_ready generator key hr
          simp [PrivacyMachine.step, hr] at h
          subst target
          simp only [extent, controlExtent]
          omega
      | none =>
          simp only [PrivacyMachine.step, hr, PMF.mem_support_map_iff] at h
          obtain ⟨generated, hg, he⟩ := h
          subst target
          have hb := generator_step generator generated hg
          simp only [extent, controlExtent]
          omega
  | source key source =>
      by_cases hh : Reification.terminal source = true
      · simp [PrivacyMachine.step, hh] at h
        subst target
        omega
      · have hf : Reification.terminal source = false := by simpa using hh
        cases ha : Reification.action code source with
        | deterministic next =>
            have hb := ControllerExtent.deterministic_action code source next hf ha
            simp [PrivacyMachine.step, hf, ha] at h
            subst target
            simp only [extent, controlExtent]
            omega
        | random zero one =>
            simp only [PrivacyMachine.step, hf, Bool.false_eq_true, ↓reduceIte, ha,
              PMF.mem_support_map_iff] at h
            obtain ⟨bit, _, he⟩ := h
            subst target
            have hb := ControllerExtent.random_action code source zero one hf ha bit
            cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte, extent, controlExtent] at * <;> omega
        | oracleCall machine request =>
            have hc := PrivacyMachine.oracleCall_control code source machine request ha
            subst source
            simp only [PrivacyMachine.step, hf, Bool.false_eq_true, ↓reduceIte, ha,
              PMF.mem_support_map_iff] at h
            obtain ⟨answer, ha, he⟩ := h
            subst target
            obtain ⟨hState, hLength⟩ := hOracle state request answer ha
            have hl := header_length (PrivacyMachine.decodeCiphertext answer.2)
            simp only [extent, controlExtent, ControllerExtent.controlExtent, responderExtent,
              ControllerExtent.traceExtent, Tape.cells, List.length_nil] at *
            omega
  | responding machine request responder =>
      cases hr : PrivacyMachine.responseOutput responder with
      | some pair =>
          rcases pair with ⟨key, output⟩
          obtain ⟨hk, ho⟩ := responder_ready responder key output hr
          simp [PrivacyMachine.step, hr] at h
          subst target
          simp only [extent, controlExtent]
          omega
      | none =>
          simp only [PrivacyMachine.step, hr, PMF.mem_support_map_iff] at h
          obtain ⟨response, hr, he⟩ := h
          subst target
          have hb := responder_step responder response hr
          simp only [extent, controlExtent]
          omega
  | rewinding key machine request tape =>
      have hb := Tape.cells_moveLeft_le tape
      cases hl : tape.left <;> simp [PrivacyMachine.step, hl] at h <;> subst target <;>
        simp only [extent, controlExtent, List.length_nil] <;> omega
  | collecting key machine request tape reversed =>
      have hb := Tape.cells_moveRight_le tape
      cases hc : tape.current <;> simp [PrivacyMachine.step, hc] at h <;> subst target <;>
        simp only [extent, controlExtent, List.length_nil, List.length_cons] <;> omega
  | reversing key machine request remaining response =>
      cases remaining <;> simp [PrivacyMachine.step] at h <;> subst target <;>
        simp only [extent, controlExtent, ControllerExtent.controlExtent, ControllerExtent.traceExtent,
          List.length_nil, List.length_cons, Tape.cells] <;> omega

noncomputable def envelope (stateSize : State → Nat) (code : PrivacyMachine.Source.Code)
    (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap) :
    TimedExecution.ResourceGrowth.Envelope (PrivacyMachine.step code oracle) where
  extent := extent stateSize
  retained := cells stateSize
  bound := bound
  monotone := bound_monotone
  covers := cells_bound stateSize
  increment := stateIncrement + responseCap + 2
  grows := fun start target h => by
    have hb := step_extent stateSize code oracle stateIncrement responseCap hOracle start target h
    omega

/-- Every possible execution prefix, including private key generation and
all authentication copies, satisfies the common retained-data envelope. -/
theorem peak (stateSize : State → Nat) (code : PrivacyMachine.Source.Code)
    (oracle : BitOracle State) (stateIncrement responseCap : Nat)
    (hOracle : ∀ state request result, result ∈ (oracle state request).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ responseCap)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start target : PrivacyMachine.Frame State)
    (h : target ∈ (PrivacyMachine.eval code oracle elapsed start).support) :
    cells stateSize target ≤ bound (extent stateSize start + horizon * (stateIncrement + responseCap + 2)) := by
  apply (envelope stateSize code oracle stateIncrement responseCap hOracle).peak
    horizon elapsed hElapsed start target
  rw [PrivacyMachine.Timing.eval_eq]
  exact h

end Foundation.Symmetric.EncryptThenMAC.PrivacyStorage
