import Foundation.Constructions.Hash.NativeSimulatorTerminalGuard

/-! Execute the fixed terminal guard and reuse the original random/remember
branch after rejection. The accepted continuation is the pending predecessor
reconstruction stage; rejection is fully implemented without a host decision. -/
namespace Foundation.Hash.Native.SimulatorNonterminalFresh
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Symmetric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n κ : Nat}

def code (terminal : Bits κ) (accepted : Code) : Code :=
  SimulatorTerminalGuard.code terminal accepted (OutputSeekFlag.code (SimulatorFresh.code n κ))

def guardSteps (k : Nat) : Nat := (1 + (2 * k + 1)) + (3 * (k + 2) + 2)

theorem guardSteps_bound (k : Nat) (hk : k < κ + 1) : guardSteps k ≤ 5 * κ + 10 := by
  unfold guardSteps
  omega

theorem rejected_run (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (terminal : Bits κ) (accepted : Code)
    (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool))
    (positive : 0 < n) (h : ¬ (query.2.1 = true ∧ query.2.2 = terminal)) :
    ∃ k, k < κ + 1 ∧
      TimedExecution.eval (Reification.timedStep (code (n := n) terminal accepted) oracle)
        (guardSteps k + SimulatorFresh.steps n κ)
        (NativeCode.frame state trace (SimulatorFresh.startAtFlag query table beforeOutput)) =
        (uniform (Bits n)).map (fun value =>
          CodeRelocation.frame (SimulatorTerminalGuard.rejectedPrefix terminal accepted).length
            (CodeRelocation.frame 4 (SimulatorFresh.finish state trace query table beforeOutput value))) := by
  have hfresh : TimedExecution.eval (Reification.timedStep (SimulatorFresh.code n κ) oracle)
      (SimulatorFresh.steps n κ) (NativeCode.frame state trace (SimulatorFresh.startAtFlag query table beforeOutput)) =
      (uniform (Bits n)).map (fun value => SimulatorFresh.finish state trace query table beforeOutput value) := by
    simpa only [SimulatorFresh.steps, SimulatorRemember.steps, Bool.toNat_true]
      using SimulatorFresh.stage_run_at_flag oracle state trace query table beforeOutput positive true
  obtain ⟨k, hk, hguard⟩ := SimulatorTerminalGuard.rejected_recovered oracle state trace terminal accepted
    (SimulatorFresh.code n κ)
    ({ Tape.ofBits (SimulatorLookup.tableBits table) with left := [none] } : Tape)
    false query beforeOutput h
  have hentry : (⟨state, .running { pc := 0, inputTape := { Tape.ofBits (SimulatorLookup.tableBits table) with left := [none] }, outputTape := { left := (compressionPacket query).reverse.map some ++ beforeOutput, current := some false, right := [none] } }, trace⟩ : Configuration State) =
      NativeCode.frame state trace (SimulatorFresh.startAtFlag query table beforeOutput) := rfl
  have hreentry : (⟨state, .running { pc := 4, inputTape := { Tape.ofBits (SimulatorLookup.tableBits table) with left := [none] }, outputTape := { left := (compressionPacket query).reverse.map some ++ beforeOutput, current := some false, right := [none] } }, trace⟩ : Configuration State) =
      CodeRelocation.frame OutputSeekFlag.scanPrefix.length
        (NativeCode.frame state trace (SimulatorFresh.startAtFlag query table beforeOutput)) := rfl
  rw [hentry, hreentry] at hguard
  refine ⟨k, hk, ?_⟩
  rw [code, guardSteps, TimedExecution.eval_add, hguard, PMF.pure_bind,
    SimulatorTerminalGuard.code_rejected_host]
  have outer := CodeRelocation.eval (SimulatorTerminalGuard.rejectedPrefix terminal accepted)
    (OutputSeekFlag.code (SimulatorFresh.code n κ)) oracle (SimulatorFresh.steps n κ)
    (CodeRelocation.frame OutputSeekFlag.scanPrefix.length
      (NativeCode.frame state trace (SimulatorFresh.startAtFlag query table beforeOutput)))
  have inner := CodeRelocation.eval OutputSeekFlag.scanPrefix (SimulatorFresh.code n κ) oracle
    (SimulatorFresh.steps n κ)
    (NativeCode.frame state trace (SimulatorFresh.startAtFlag query table beforeOutput))
  rw [hfresh] at inner
  rw [outer]
  simp only [OutputSeekFlag.code] at ⊢
  rw [inner, PMF.map_comp, PMF.map_comp]
  rfl

/-- The same rejection branch starts from the real failed-lookup entry, with the
table rewind and both flag/key movements charged. -/
theorem rejected_after_rewind (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) (terminal : Bits κ) (accepted : Code)
    (query : CompressionInput (Bits κ) (Bits n))
    (table : CompressionTable (Bits κ) (Bits n)) (beforeOutput : List (Option Bool))
    (fresh : table.lookup query = none) (positive : 0 < n)
    (h : ¬ (query.2.1 = true ∧ query.2.2 = terminal)) :
    ∃ k, k < κ + 1 ∧
      TimedExecution.eval (Reification.timedStep
        (SimulatorFreshAfterLookup.codeWithBody (code (n := n) terminal accepted)) oracle)
        (SimulatorFreshAfterLookup.rewindSteps table + 1 + (guardSteps k + SimulatorFresh.steps n κ))
        (NativeCode.frame state trace (SimulatorFreshAfterLookup.start query table beforeOutput)) =
        (uniform (Bits n)).map (fun value => CodeRelocation.frame 5 (CodeRelocation.frame 1
          (CodeRelocation.frame (SimulatorTerminalGuard.rejectedPrefix terminal accepted).length
            (CodeRelocation.frame 4 (SimulatorFresh.finish state trace query table beforeOutput value))))) := by
  obtain ⟨k, hk, hbody⟩ := rejected_run oracle state trace terminal accepted query table beforeOutput positive h
  refine ⟨k, hk, ?_⟩
  rw [SimulatorFreshAfterLookup.withBody_run (code (n := n) terminal accepted) oracle state trace
    query table beforeOutput fresh, hbody, PMF.map_comp]
  rfl

end Foundation.Hash.Native.SimulatorNonterminalFresh
