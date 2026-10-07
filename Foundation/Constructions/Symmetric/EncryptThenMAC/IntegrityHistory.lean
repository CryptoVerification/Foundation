import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityGameObservation

/-! The real signing history is identified with successful public responses.
This invariant concerns complete ciphertext/tag pairs, including chronological
order. It is proved for arbitrary finite source execution and oracle state. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
open Machine Foundation.Probability IntegrityGameCodec
set_option backward.isDefEq.respectTransparency false

def signedHistory (width : Nat) (trace : List (Bool × List Bool)) : List (Bool × Bits width) :=
  trace.reverse.map (fun pair => (pair.1, decodeTag width pair.2))

def publicHistory (width : Nat) (trace : List (List Bool × List Bool)) : List (Bool × Bits width) :=
  trace.reverse.filterMap (fun pair => decodeResponse width pair.2)

def HistoryInvariant (width : Nat) (frame : LogicalFrame State) : Prop :=
  signedHistory width frame.signingTrace = publicHistory width frame.sourceTrace

theorem logicalQuery_history (oracle : State → Bool → PMF (State × List Bool)) (key : Bool)
    (machine : Configuration) (request : List Bool) (width : Nat) (start final : LogicalFrame State)
    (hStart : HistoryInvariant width start) (hFinal : final ∈ (logicalQuery oracle key machine request start).support) :
    HistoryInvariant width final := by
  cases hu : start.used with
  | true =>
      simp only [logicalQuery, hu, ↓reduceIte, PMF.mem_support_pure_iff] at hFinal
      subst final
      simpa [HistoryInvariant, publicHistory, decodeResponse, List.reverse_cons, List.filterMap_append] using hStart
  | false =>
      simp only [logicalQuery, hu, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at hFinal
      obtain ⟨answer, _, he⟩ := hFinal
      subst final
      change signedHistory width start.signingTrace = publicHistory width start.sourceTrace at hStart
      simpa [HistoryInvariant, signedHistory, publicHistory, decodeResponse,
        List.reverse_cons, List.map_append] using hStart

theorem logicalStep_history (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (width : Nat) (start final : LogicalFrame State)
    (hStart : HistoryInvariant width start) (hFinal : final ∈ (logicalStep code oracle key start).support) :
    HistoryInvariant width final := by
  by_cases ht : CryptoOracle.Interactive.Reification.terminal start.control = true
  · simp only [logicalStep, ht, ↓reduceIte, PMF.mem_support_pure_iff] at hFinal
    subst final
    exact hStart
  · cases ha : CryptoOracle.Interactive.Reification.action code start.control with
    | deterministic next =>
        simp only [logicalStep, ht, Bool.false_eq_true, ↓reduceIte, ha, PMF.mem_support_pure_iff] at hFinal
        subst final
        exact hStart
    | random zero one =>
        simp only [logicalStep, ht, Bool.false_eq_true, ↓reduceIte, ha, PMF.mem_support_map_iff] at hFinal
        obtain ⟨bit, _, he⟩ := hFinal
        subst final
        exact hStart
    | oracleCall machine request =>
        simp only [logicalStep, ht, Bool.false_eq_true, ↓reduceIte, ha] at hFinal
        exact logicalQuery_history oracle key machine request width start final hStart hFinal

theorem logical_eval_history (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (width count : Nat) (start final : LogicalFrame State)
    (hStart : HistoryInvariant width start)
    (hFinal : final ∈ (TimedExecution.eval (logicalStep code oracle key) count start).support) :
    HistoryInvariant width final := by
  induction count generalizing start with
  | zero =>
      simp only [TimedExecution.eval, PMF.mem_support_pure_iff] at hFinal
      subst final
      exact hStart
  | succ count ih =>
      rw [TimedExecution.eval, PMF.mem_support_bind_iff] at hFinal
      obtain ⟨middle, hMiddle, hFinal⟩ := hFinal
      exact ih middle (logicalStep_history code oracle key width start middle hStart hMiddle) hFinal

theorem logicalInitial_history (width : Nat) (state : State) (input : List Bool) :
    HistoryInvariant width (logicalInitial state input) := rfl

theorem native_history (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (width : Nat) (hTags : TagLength oracle width) (count : Nat) (start : LogicalFrame State)
    (hStart : HistoryInvariant width start)
    (hStops : CryptoOracle.Interactive.Reification.HaltsWithin code (sourceOracle oracle key) start.view count)
    (final : Frame State)
    (hFinal : final ∈ (eval code oracle (count * (5 * width + 36)) (LogicalFrame.embed key start)).support) :
    signedHistory width final.signingTrace = publicHistory width final.sourceTrace := by
  rw [realized_source_execution code oracle key width hTags count start hStops, PMF.mem_support_map_iff] at hFinal
  obtain ⟨source, hSource, he⟩ := hFinal
  subst final
  exact logical_eval_history code oracle key width count start source hStart hSource

theorem initialized_native_history (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (width : Nat) (hTags : TagLength oracle width) (count : Nat) (state : State) (input : List Bool)
    (hStops : ∀ key ∈ sampleBit.support, CryptoOracle.Interactive.Reification.HaltsWithin code
      (sourceOracle oracle key) (logicalInitial state input).view count)
    (final : Frame State) (hFinal : final ∈ (eval code oracle (executionBudget width count) (initial state input)).support) :
    signedHistory width final.signingTrace = publicHistory width final.sourceTrace := by
  rw [initialized_source_execution code oracle width hTags count state input
    (fun key hKey => logical_stops_of_source code oracle key count (logicalInitial state input) (hStops key hKey)),
    PMF.mem_support_bind_iff] at hFinal
  obtain ⟨key, hKey, hMap⟩ := hFinal
  rw [PMF.mem_support_map_iff] at hMap
  obtain ⟨source, hSource, he⟩ := hMap
  subst final
  exact logical_eval_history code oracle key width count (logicalInitial state input) source
    (logicalInitial_history width state input) hSource

end Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
