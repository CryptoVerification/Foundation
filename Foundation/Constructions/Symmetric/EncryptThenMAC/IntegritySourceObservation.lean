import Foundation.Constructions.Symmetric.EncryptThenMAC.IntegritySourceExecution
import Foundation.Crypto.Semantics.Oracle.ReificationExecution

/-! Observe the real integrity controller as the existing interactive source
machine. Signing state, encryption exhaustion and the signing transcript are
opaque oracle state; the source controller receives only response bytes. -/
namespace Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
open Machine Foundation.Probability
set_option backward.isDefEq.respectTransparency false

abbrev SourceState (State : Type u) := State × Bool × List (Bool × List Bool)

def LogicalFrame.view (frame : LogicalFrame State) : CryptoOracle.Interactive.Configuration (SourceState State) :=
  ⟨(frame.state, frame.used, frame.signingTrace), frame.control, frame.sourceTrace⟩

noncomputable def sourceOracle (oracle : State → Bool → PMF (State × List Bool)) (key : Bool) :
    CryptoOracle.Interactive.BitOracle (SourceState State) :=
  fun state request =>
    if state.2.1 then PMF.pure ((state.1, true, state.2.2), [false])
    else
      let ciphertext := Bool.xor key (request.headD false)
      (oracle state.1 ciphertext).map (fun answer =>
        ((answer.1, true, (ciphertext, answer.2) :: state.2.2), true :: ciphertext :: answer.2))

theorem logicalStep_view (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (frame : LogicalFrame State) :
    (logicalStep code oracle key frame).map LogicalFrame.view =
      if CryptoOracle.Interactive.Reification.terminal frame.control then PMF.pure frame.view
      else CryptoOracle.Interactive.Reification.perform code (sourceOracle oracle key) frame.view := by
  by_cases ht : CryptoOracle.Interactive.Reification.terminal frame.control = true
  · simp [logicalStep, ht, PMF.pure_map]
  · cases ha : CryptoOracle.Interactive.Reification.action code frame.control with
    | deterministic next =>
        simp [logicalStep, ht, ha, LogicalFrame.view, CryptoOracle.Interactive.Reification.perform, PMF.pure_map]
    | random zero one =>
        simp [logicalStep, ht, ha, LogicalFrame.view, CryptoOracle.Interactive.Reification.perform,
          PMF.map_comp, Function.comp_def]
    | oracleCall machine request =>
        cases hu : frame.used <;>
          simp [logicalStep, ht, ha, LogicalFrame.view, CryptoOracle.Interactive.Reification.perform,
            sourceOracle, logicalQuery, hu, PMF.pure_map, PMF.map_comp, Function.comp_def]

theorem logical_eval_view (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (count : Nat) (frame : LogicalFrame State) :
    (TimedExecution.eval (logicalStep code oracle key) count frame).map LogicalFrame.view =
      CryptoOracle.Interactive.Reification.eval code (sourceOracle oracle key) count frame.view := by
  rw [← CryptoOracle.Interactive.Reification.timed_eval_eq]
  exact TimedExecution.eval_map _ _ LogicalFrame.view
    (fun frame => by
      simpa only [CryptoOracle.Interactive.Reification.timedStep, LogicalFrame.view] using
        logicalStep_view code oracle key frame) count frame

theorem logical_stops_of_source (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (count : Nat) (start : LogicalFrame State)
    (h : CryptoOracle.Interactive.Reification.HaltsWithin code (sourceOracle oracle key) start.view count) :
    ∀ final ∈ (TimedExecution.eval (logicalStep code oracle key) count start).support,
      CryptoOracle.Interactive.Reification.terminal final.control = true := by
  intro final hFinal
  apply h final.view
  rw [← logical_eval_view, PMF.mem_support_map_iff]
  exact ⟨final, hFinal, rfl⟩

theorem realized_source_execution (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (width : Nat) (hTags : TagLength oracle width) (count : Nat) (start : LogicalFrame State)
    (h : CryptoOracle.Interactive.Reification.HaltsWithin code (sourceOracle oracle key) start.view count) :
    eval code oracle (count * (5 * width + 36)) (LogicalFrame.embed key start) =
      (TimedExecution.eval (logicalStep code oracle key) count start).map (LogicalFrame.embed key) :=
  source_execution code oracle key width hTags count start (logical_stops_of_source code oracle key count start h)
    _ (Nat.le_refl _)

def sourceView (frame : Frame State) : Option (CryptoOracle.Interactive.Configuration (SourceState State)) :=
  match frame.control with
  | .source _ used control => some ⟨(frame.state, used, frame.signingTrace), control, frame.sourceTrace⟩
  | _ => none

theorem source_observation (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (key : Bool) (width : Nat) (hTags : TagLength oracle width) (count : Nat) (start : LogicalFrame State)
    (h : CryptoOracle.Interactive.Reification.HaltsWithin code (sourceOracle oracle key) start.view count) :
    (eval code oracle (count * (5 * width + 36)) (LogicalFrame.embed key start)).map sourceView =
      (CryptoOracle.Interactive.Reification.eval code (sourceOracle oracle key) count start.view).map some := by
  rw [realized_source_execution code oracle key width hTags count start h, PMF.map_comp,
    ← logical_eval_view code oracle key count start, PMF.map_comp]
  rfl

theorem initialized_source_observation (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (width : Nat) (hTags : TagLength oracle width) (count : Nat) (state : State) (input : List Bool)
    (hStops : ∀ key ∈ sampleBit.support, CryptoOracle.Interactive.Reification.HaltsWithin code
      (sourceOracle oracle key) (logicalInitial state input).view count) :
    (eval code oracle (executionBudget width count) (initial state input)).map sourceView =
      sampleBit.bind (fun key =>
        (CryptoOracle.Interactive.Reification.eval code (sourceOracle oracle key)
          count (logicalInitial state input).view).map some) := by
  rw [initialized_source_execution code oracle width hTags count state input
      (fun key hKey => logical_stops_of_source code oracle key count (logicalInitial state input) (hStops key hKey)),
    PMF.map_bind]
  congr 1
  funext key
  rw [PMF.map_comp, ← logical_eval_view code oracle key count (logicalInitial state input), PMF.map_comp]
  rfl

theorem initialized_source_stops (code : SourceCode) (oracle : State → Bool → PMF (State × List Bool))
    (width : Nat) (hTags : TagLength oracle width) (count : Nat) (state : State) (input : List Bool)
    (hStops : ∀ key ∈ sampleBit.support, CryptoOracle.Interactive.Reification.HaltsWithin code
      (sourceOracle oracle key) (logicalInitial state input).view count) :
    HaltsWithin code oracle (initial state input) (executionBudget width count) :=
  initialized_source_haltsWithin code oracle width hTags count state input
    (fun key hKey => logical_stops_of_source code oracle key count (logicalInitial state input) (hStops key hKey))

end Foundation.Symmetric.EncryptThenMAC.IntegrityMachine
