import Foundation.Constructions.Symmetric.EncryptThenMAC.PrivacySourceExecution
import Foundation.Crypto.Semantics.Oracle.ReificationExecution

/-! Identify the proof-level source execution with the existing finite
interactive source machine. Layout is erased; external raw history is opaque
oracle state, and the source transcript contains authenticated responses. -/
namespace Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
open Machine Foundation.Probability
universe u
set_option backward.isDefEq.respectTransparency false

def LogicalFrame.view {State : Type u} (frame : LogicalFrame State) :
    CryptoOracle.Interactive.Configuration (State × List (List Bool × List Bool)) :=
  ⟨(frame.state, frame.externalTrace), frame.control, frame.sourceTrace⟩

noncomputable def authenticatedOracle {State : Type u} {width : Nat}
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : TableMAC.Key width) :
    CryptoOracle.Interactive.BitOracle (State × List (List Bool × List Bool)) :=
  fun state request => (oracle state.1 request).map fun answer =>
    ((answer.1, (request, answer.2) :: state.2),
      AuthenticateResponse.encode ((decodeCiphertext answer.2).map (fun bit => (bit, TableMAC.sign key bit))))

theorem logicalStep_view {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : TableMAC.Key width) (frame : LogicalFrame State) :
    (logicalStep code oracle key frame).map LogicalFrame.view =
      if CryptoOracle.Interactive.Reification.terminal frame.control then PMF.pure frame.view
      else CryptoOracle.Interactive.Reification.perform code (authenticatedOracle oracle key) frame.view := by
  by_cases ht : CryptoOracle.Interactive.Reification.terminal frame.control = true
  · simp [logicalStep, ht, PMF.pure_map]
  · cases ha : CryptoOracle.Interactive.Reification.action code frame.control <;>
      simp [logicalStep, ht, ha, LogicalFrame.view, CryptoOracle.Interactive.Reification.perform,
        authenticatedOracle, queryResult, PMF.pure_map, PMF.map_comp, Function.comp_def]

theorem logical_eval_view {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : TableMAC.Key width)
    (count : Nat) (frame : LogicalFrame State) :
    (TimedExecution.eval (logicalStep code oracle key) count frame).map LogicalFrame.view =
      CryptoOracle.Interactive.Reification.eval code (authenticatedOracle oracle key) count frame.view := by
  rw [← CryptoOracle.Interactive.Reification.timed_eval_eq]
  exact TimedExecution.eval_map _ _ LogicalFrame.view
    (fun frame => by
      simpa only [CryptoOracle.Interactive.Reification.timedStep, LogicalFrame.view] using
        logicalStep_view code oracle key frame) count frame

/-- Transfer the ordinary source-machine stopping witness; no new stopping
predicate on a different logical machine need be assumed by the caller. -/
theorem logical_stops_of_source {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : TableMAC.Key width)
    (count : Nat) (start : LogicalFrame State)
    (h : CryptoOracle.Interactive.Reification.HaltsWithin code (authenticatedOracle oracle key) start.view count) :
    ∀ final ∈ (TimedExecution.eval (logicalStep code oracle key) count start).support,
      CryptoOracle.Interactive.Reification.terminal final.control = true := by
  intro final hFinal
  apply h final.view
  rw [← logical_eval_view, PMF.mem_support_map_iff]
  exact ⟨final, hFinal, rfl⟩

theorem realized_source_execution {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : TableMAC.Key width)
    (count : Nat) (start : LogicalFrame State)
    (h : CryptoOracle.Interactive.Reification.HaltsWithin code (authenticatedOracle oracle key) start.view count) :
    eval code oracle (count * (29 * width + 39)) (LogicalFrame.embed key start) =
      (TimedExecution.eval (logicalStep code oracle key) count start).map (LogicalFrame.embed key) :=
  source_execution code oracle key count start (logical_stops_of_source code oracle key count start h)
    _ (Nat.le_refl _)

def sourceView {State : Type u} (frame : Frame State) :
    Option (CryptoOracle.Interactive.Configuration (State × List (List Bool × List Bool))) :=
  match frame.control with
  | .source _ control => some ⟨(frame.state, frame.externalTrace), control, frame.sourceTrace⟩
  | _ => none

/-- Erase the private key and its proof-only layout. The actual whole
machine and the ordinary interactive source have the same joint observation. -/
theorem source_observation {State : Type u} {width : Nat} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (key : TableMAC.Key width)
    (count : Nat) (start : LogicalFrame State)
    (h : CryptoOracle.Interactive.Reification.HaltsWithin code (authenticatedOracle oracle key) start.view count) :
    (eval code oracle (count * (29 * width + 39)) (LogicalFrame.embed key start)).map sourceView =
      (CryptoOracle.Interactive.Reification.eval code (authenticatedOracle oracle key) count start.view).map some := by
  rw [realized_source_execution code oracle key count start h, PMF.map_comp,
    ← logical_eval_view code oracle key count start, PMF.map_comp]
  rfl

/-- Initialization plus arbitrary source execution, observed without the
private key. The stopping premise is the existing source machine's witness. -/
theorem initialized_source_observation {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (width : Nat → Nat) (n count : Nat)
    (state : State) (input : List Bool)
    (hStops : ∀ key ∈ ((TableMAC.scheme width).keygen n).support,
      CryptoOracle.Interactive.Reification.HaltsWithin code (authenticatedOracle oracle key)
        (logicalInitial state input).view count) :
    (eval code oracle (executionBudget (width n) count)
      (initial state (List.replicate (2 * width n) true) input)).map sourceView =
      ((TableMAC.scheme width).keygen n).bind (fun key =>
        (CryptoOracle.Interactive.Reification.eval code (authenticatedOracle oracle key)
          count (logicalInitial state input).view).map some) := by
  rw [initialized_source_execution code oracle width n count state input
      (fun key hKey => logical_stops_of_source code oracle key count (logicalInitial state input) (hStops key hKey)),
    PMF.map_bind]
  congr 1
  funext key
  rw [PMF.map_comp, ← logical_eval_view code oracle key count (logicalInitial state input), PMF.map_comp]
  rfl

theorem initialized_source_stops {State : Type u} (code : Source.Code)
    (oracle : CryptoOracle.Interactive.BitOracle State) (width : Nat → Nat) (n count : Nat)
    (state : State) (input : List Bool)
    (hStops : ∀ key ∈ ((TableMAC.scheme width).keygen n).support,
      CryptoOracle.Interactive.Reification.HaltsWithin code (authenticatedOracle oracle key)
        (logicalInitial state input).view count) :
    HaltsWithin code oracle (initial state (List.replicate (2 * width n) true) input)
      (executionBudget (width n) count) :=
  initialized_source_haltsWithin code oracle width n count state input
    (fun key hKey => logical_stops_of_source code oracle key count (logicalInitial state input) (hStops key hKey))

end Foundation.Symmetric.EncryptThenMAC.PrivacyMachine
