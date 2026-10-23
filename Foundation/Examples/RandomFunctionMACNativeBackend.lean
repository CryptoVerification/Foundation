import Foundation.Constructions.Hash.NativeCompactMACExecutionCorrectness

/-! Concrete empty-cache instantiation of the unchanged 251-instruction MAC
caller with the real compact native backend. This establishes execution,
stopping and the protocol shape; the full probability/security refinement
of this backend execution is a separate obligation. -/
namespace Foundation.Symmetric.RandomFunctionMACNativeCaller.NativeBackend
open Machine CryptoOracle CryptoOracle.Interactive Foundation.Probability TimedExecution
open Foundation.Hash.Native CompactMACRound CompactMACExecution
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

variable {State Source : Type}

/-- The empty table contains its actual false end marker on the private tape. -/
def emptyMachine : Machine.Configuration := {inputTape := Tape.ofBits [false]}

def empty (serverState : State) (serverTrace : List (List Bool × List Bool)) : Retained State where
  table := []
  saved := NativeCode.frame serverState serverTrace emptyMachine
  machine := emptyMachine
  hControl := rfl
  tableLayout := Machine.Tape.Equivalent.refl _

variable (oracle : BitOracle State) (callerOracle : BitOracle Source)
    (serverState : State) (callerState : Source)
    (serverTrace callerTrace : List (List Bool × List Bool))

theorem empty_run :
    TimedExecution.eval (CompactMACRound.step oracle callerOracle) 2091
      (.source (NativeCode.frame serverState serverTrace emptyMachine) ⟨callerState, .running {}, callerTrace⟩) =
      ((whole oracle callerOracle (empty serverState serverTrace) callerState callerTrace).semantics ()).map embed :=
  whole_run oracle callerOracle (empty serverState serverTrace) callerState callerTrace 2091 (by simp [empty])

theorem empty_halts (final : CompactMACRound.Control State Source)
    (supported : final ∈ (TimedExecution.eval (CompactMACRound.step oracle callerOracle) 2091
      (.source (NativeCode.frame serverState serverTrace emptyMachine) ⟨callerState, .running {}, callerTrace⟩)).support) :
    ∃ (saved : Configuration State) (actual : Machine.Configuration) (history : List (List Bool × List Bool)),
      final = .source saved ⟨callerState, .running actual, history⟩ ∧ actual.halted = true ∧
      history.length = callerTrace.length + 4 := by
  rw [empty_run, PMF.mem_support_map_iff] at supported
  obtain ⟨output, supported, rfl⟩ := supported
  obtain ⟨⟨actual, hc, halted⟩, state, length, _⟩ := whole_post oracle callerOracle
    (empty serverState serverTrace) callerState callerTrace output supported
  exact ⟨output.1.saved, actual, output.2.reverseTrace,
    by cases output with | mk retained frame => cases frame; simp_all [embed], halted, length⟩

theorem empty_actual_cost (result : Output State Source × Nat)
    (supported : result ∈ ((whole oracle callerOracle (empty serverState serverTrace) callerState callerTrace).costed ()).support) :
    embed result.1 ∈ (TimedExecution.eval (CompactMACRound.step oracle callerOracle) result.2
      (.source (NativeCode.frame serverState serverTrace emptyMachine) ⟨callerState, .running {}, callerTrace⟩)).support ∧
    result.2 ≤ 2091 ∧ Post (empty serverState serverTrace) callerState callerTrace 4 result.1 := by
  simpa only [empty, List.length_nil, Nat.mul_zero, Nat.zero_add] using
    whole_costed oracle callerOracle (empty serverState serverTrace) callerState callerTrace result supported

end Foundation.Symmetric.RandomFunctionMACNativeCaller.NativeBackend
