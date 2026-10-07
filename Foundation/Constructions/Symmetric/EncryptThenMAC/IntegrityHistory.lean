import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegrityGameObservation
import Foundation.Crypto.Semantics.Invariant
import Foundation.Crypto.Semantics.Oracle.History

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
  change Foundation.History.Agreement (fun pair => (pair.1, decodeTag width pair.2))
    (fun pair => decodeResponse width pair.2) start.signingTrace start.sourceTrace at hStart
  cases hu : start.used with
  | true =>
      simp only [logicalQuery, hu, ↓reduceIte, PMF.mem_support_pure_iff] at hFinal
      subst final
      exact Foundation.History.failure _ _ _ _ (request, [false]) hStart rfl
  | false =>
      simp only [logicalQuery, hu, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at hFinal
      obtain ⟨answer, _, he⟩ := hFinal
      subst final
      exact Foundation.History.success _ _ _ _
        (Bool.xor key (request.headD false), answer.2)
        (request, true :: Bool.xor key (request.headD false) :: answer.2) hStart rfl

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
  exact TimedExecution.eval_preserves _ _
    (fun start hStart final hFinal => logicalStep_history code oracle key width start final hStart hFinal)
    count start final hStart hFinal

theorem logicalInitial_history (width : Nat) (state : State) (input : List Bool) :
    HistoryInvariant width (logicalInitial state input) := rfl

theorem native_history (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (width : Nat) (hTags : TagLength oracle width) (count : Nat) (start : LogicalFrame State)
    (hStart : HistoryInvariant width start)
    (hStops : CryptoOracle.Interactive.Reification.HaltsWithin code (sourceOracle oracle key) start.view count)
    (final : Frame State)
    (hFinal : final ∈ (eval code oracle (count * (5 * width + 36)) (LogicalFrame.embed key start)).support) :
    signedHistory width final.signingTrace = publicHistory width final.sourceTrace := by
  exact TimedExecution.realized_invariant _ _ (LogicalFrame.embed key)
    (fun frame : Frame State => signedHistory width frame.signingTrace = publicHistory width frame.sourceTrace)
    (realized_source_execution code oracle key width hTags count start hStops)
    (fun source hSource => logical_eval_history code oracle key width count start source hStart hSource)
    final hFinal

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
