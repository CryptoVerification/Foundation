import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityStorage
import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegritySourceExecution
import Foundation.Crypto.Semantics.Oracle.SourceActionExtent

/-! Local extent bounds for every real integrity-controller transition,
including generation, encryption, signing, copies and history updates. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityStorage
open Machine Foundation.Probability CryptoOracle.Interactive
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {State : Type u}

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

private theorem native_action_bound (stateSize : State → Nat)
    (oracle : State → Bool → PMF (State × List Bool)) (state : State)
    (program : Program) (machine : Machine.Configuration)
    (embed : Machine.Configuration → IntegrityMachine.Frame State) (cap : Nat)
    (hEmbed : ∀ target, Machine.ControllerExtent.machine target ≤ Machine.ControllerExtent.machine machine + 1 →
      extent stateSize (embed target) ≤ cap)
    (target : IntegrityMachine.Frame State)
    (h : target ∈ (runAction oracle state (IntegrityMachine.nativeAction program machine embed)).support) :
    extent stateSize target ≤ cap := by
  rw [native_action_run, PMF.mem_support_map_iff] at h
  obtain ⟨machine', hm, he⟩ := h
  subst target
  exact hEmbed machine' (Machine.ControllerExtent.native_bound program machine machine' hm)

private theorem prepare_extent (used key message : Bool) (phase : Nat) (tape : Tape) :
    preparationExtent (IntegrityPreparation.prepareNext used key message phase tape) ≤ tape.cells + 1 := by
  have hl := Tape.cells_moveLeft_le tape
  have hr := Tape.cells_moveRight_le tape
  unfold IntegrityPreparation.prepareNext
  split <;> simp only [preparationExtent, Tape.cells_write]
  all_goals first | omega | (change max tape.cells 1 ≤ tape.cells + 1; omega)

theorem step_extent (stateSize : State → Nat) (code : IntegrityMachine.SourceCode)
    (oracle : State → Bool → PMF (State × List Bool)) (stateIncrement tagCap : Nat)
    (hOracle : ∀ state ciphertext result, result ∈ (oracle state ciphertext).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ tagCap)
    (start target : IntegrityMachine.Frame State)
    (h : target ∈ (IntegrityMachine.step code oracle start).support) :
    extent stateSize target ≤ extent stateSize start + stateIncrement + tagCap + 2 := by
  rcases start with ⟨state, control, sourceTrace, tags⟩
  have hs := ControllerExtent.trace_length sourceTrace
  have ht := ControllerExtent.trace_length (signingTrace tags)
  cases control with
  | initializing source generator =>
      by_cases hh : generator.halted = true
      · simp [IntegrityMachine.step, IntegrityMachine.transition, hh] at h
        subst target
        simp only [extent, controlExtent]
        omega
      · simp only [IntegrityMachine.step, IntegrityMachine.transition, hh, Bool.false_eq_true, ↓reduceIte] at h
        apply native_action_bound stateSize oracle state _ generator _ _ ?_ target h
        intro machine hm
        simp only [extent, controlExtent]
        omega
  | source key used source =>
      by_cases hh : Reification.terminal source = true
      · simp [IntegrityMachine.step, IntegrityMachine.transition, hh] at h
        subst target
        omega
      · have hf : Reification.terminal source = false := by simpa using hh
        cases ha : Reification.action code source with
        | deterministic next =>
            have hb := ControllerExtent.deterministic_action code source next hf ha
            simp [IntegrityMachine.step, IntegrityMachine.transition, hf, ha] at h
            subst target
            simp only [extent, controlExtent]
            omega
        | random zero one =>
            simp only [IntegrityMachine.step, IntegrityMachine.transition, hf, Bool.false_eq_true,
              ↓reduceIte, ha, PMF.mem_support_map_iff] at h
            obtain ⟨bit, _, he⟩ := h
            subst target
            have hb := ControllerExtent.random_action code source zero one hf ha bit
            cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte, extent, controlExtent] at * <;> omega
        | oracleCall machine request =>
            have hc := IntegrityMachine.source_oracleCall_control code source machine request ha
            subst source
            simp [IntegrityMachine.step, IntegrityMachine.transition, hf, ha] at h
            subst target
            simp only [extent, controlExtent, ControllerExtent.controlExtent,
              preparationExtent, IntegrityPreparation.initial, Tape.cells, List.length_nil]
            omega
  | encrypting key used machine request preparation =>
      cases hr : IntegrityPreparation.ready preparation with
      | some result =>
          rcases result with ⟨newUsed, ciphertext⟩
          cases ciphertext with
          | none =>
              simp [IntegrityMachine.step, IntegrityMachine.transition, hr] at h
              subst target
              simp only [extent, controlExtent]
              omega
          | some ciphertext =>
              simp only [IntegrityMachine.step, IntegrityMachine.transition, hr, PMF.mem_support_map_iff] at h
              obtain ⟨answer, ha, he⟩ := h
              subst target
              obtain ⟨hState, hLength⟩ := hOracle state ciphertext answer ha
              simp only [extent, controlExtent, signingTrace, List.map_cons,
                ControllerExtent.traceExtent, List.length_cons, List.length_nil, Tape.cells] at *
              omega
      | none =>
          cases preparation with
          | preparing phase tape =>
              have hp := prepare_extent used key (request.head?.getD false) phase tape
              simp [IntegrityMachine.step, IntegrityMachine.transition, hr] at h
              subst target
              simp only [extent, controlExtent, preparationExtent] at *
              omega
          | encrypting native =>
              simp only [IntegrityMachine.step, IntegrityMachine.transition, hr] at h
              apply native_action_bound stateSize oracle state _ native _ _ ?_ target h
              intro next hn
              simp only [extent, controlExtent, preparationExtent]
              omega
  | failure key machine request =>
      simp [IntegrityMachine.step, IntegrityMachine.transition] at h
      subst target
      simp only [extent, controlExtent, Tape.cells_write, Tape.write, Tape.cells, List.length_nil]
      omega
  | header key machine request ciphertext tag phase tape =>
      have hm := Tape.cells_moveRight_le tape
      simp only [IntegrityMachine.step, IntegrityMachine.transition] at h
      split at h <;> simp only [PMF.mem_support_pure_iff] at h <;> subst target <;>
        simp only [extent, controlExtent, Tape.cells_write] <;> omega
  | copying key machine request remaining tape =>
      cases remaining <;> simp [IntegrityMachine.step, IntegrityMachine.transition] at h <;> subst target <;>
        simp only [extent, controlExtent, List.length_cons, Tape.cells_write] <;> omega
  | advancing key machine request remaining tape =>
      have hm := Tape.cells_moveRight_le tape
      simp [IntegrityMachine.step, IntegrityMachine.transition] at h
      subst target
      simp only [extent, controlExtent]
      omega
  | rewinding key machine request tape =>
      have hm := Tape.cells_moveLeft_le tape
      cases hl : tape.left <;> simp [IntegrityMachine.step, IntegrityMachine.transition, hl] at h <;> subst target <;>
        simp only [extent, controlExtent, List.length_nil] <;> omega
  | collecting key machine request tape reversed =>
      have hm := Tape.cells_moveRight_le tape
      cases hc : tape.current <;> simp [IntegrityMachine.step, IntegrityMachine.transition, hc] at h <;> subst target <;>
        simp only [extent, controlExtent, List.length_nil, List.length_cons] <;> omega
  | reversing key machine request remaining response =>
      cases remaining <;> simp [IntegrityMachine.step, IntegrityMachine.transition] at h <;> subst target <;>
        simp only [extent, controlExtent, ControllerExtent.controlExtent, ControllerExtent.traceExtent,
          List.length_nil, List.length_cons, Tape.cells] <;> omega

noncomputable def envelope (stateSize : State → Nat) (code : IntegrityMachine.SourceCode)
    (oracle : State → Bool → PMF (State × List Bool)) (stateIncrement tagCap : Nat)
    (hOracle : ∀ state ciphertext result, result ∈ (oracle state ciphertext).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ tagCap) :
    TimedExecution.ResourceGrowth.Envelope (IntegrityMachine.step code oracle) where
  extent := extent stateSize
  retained := cells stateSize
  bound := bound
  monotone := bound_monotone
  covers := cells_bound stateSize
  increment := stateIncrement + tagCap + 2
  grows := fun start target h => by
    have hb := step_extent stateSize code oracle stateIncrement tagCap hOracle start target h
    omega

/-- Every supported intermediate state, including temporary copies and both
transcripts, obeys the same polynomial envelope. -/
theorem peak (stateSize : State → Nat) (code : IntegrityMachine.SourceCode)
    (oracle : State → Bool → PMF (State × List Bool)) (stateIncrement tagCap : Nat)
    (hOracle : ∀ state ciphertext result, result ∈ (oracle state ciphertext).support →
      stateSize result.1 ≤ stateSize state + stateIncrement ∧ result.2.length ≤ tagCap)
    (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon)
    (start target : IntegrityMachine.Frame State)
    (h : target ∈ (IntegrityMachine.eval code oracle elapsed start).support) :
    cells stateSize target ≤ bound (extent stateSize start + horizon * (stateIncrement + tagCap + 2)) :=
  (envelope stateSize code oracle stateIncrement tagCap hOracle).peak horizon elapsed hElapsed start target h

end Foundation.Symmetric.EncryptThenMAC.IntegrityStorage
