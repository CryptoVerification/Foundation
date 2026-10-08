import Foundation.Crypto.Semantics.Machine.NativeCellResponseEquivalent
import Foundation.Crypto.Semantics.Oracle.ResponseLoading

/-! A fixed controller loads a raw request cell by cell, hands off the actual
loaded tape, and executes/export a fixed native component. Logical decoding
is used only in the proof contract, never by the runtime transition. -/
namespace Machine.NativePacketService
open Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false

inductive Control where
  | loading (remaining : List Bool) (tape : Tape)
  | advancing (remaining : List Bool) (tape : Tape)
  | rewinding (tape : Tape)
  | prepared (machine : Configuration)
  | executing (component : ResponseExport.Control)

noncomputable def step (code : Program) : Control → PMF Control
  | .loading [] tape => PMF.pure (.rewinding tape)
  | .loading (bit :: rest) tape => PMF.pure (.advancing rest (tape.write (some bit)))
  | .advancing rest tape => PMF.pure (.loading rest tape.moveRight)
  | .rewinding tape =>
      match tape.left with
      | [] => PMF.pure (.prepared {outputTape := tape})
      | _ :: _ => PMF.pure (.rewinding tape.moveLeft)
  | .prepared machine => PMF.pure (.executing (.running machine))
  | .executing component => (CellResponseExport.step code component).map .executing

def loaded (request : List Bool) : Configuration :=
  { outputTape := CryptoOracle.Interactive.ResponseLoading.loaded request }

theorem writing (code : Program) (remaining before : List Bool) :
    eval (step code) (2 * remaining.length + 1)
      (.loading remaining {left := before.reverse.map some}) =
      PMF.pure (.rewinding {left := (before ++ remaining).reverse.map some}) := by
  induction remaining generalizing before with
  | nil => simp [eval, step]
  | cons bit rest ih =>
      rw [show 2 * (bit :: rest).length + 1 = ((2 * rest.length + 1) + 1) + 1 by simp; omega, eval]
      simp only [step, PMF.pure_bind]
      rw [eval]
      simp only [step, PMF.pure_bind]
      simpa [Tape.write, Tape.moveRight, List.reverse_append, List.map_append,
        List.append_assoc] using ih (before ++ [bit])

theorem rewind (code : Program) (left : List Bool) (current : Option Bool) (right : List (Option Bool)) :
    eval (step code) (left.length + 1) (.rewinding ⟨left.map some, current, right⟩) =
      PMF.pure (.prepared {outputTape :=
        CryptoOracle.Interactive.ResponseLoading.fromCells (left.reverse.map some ++ current :: right)}) := by
  induction left generalizing current right with
  | nil => simp [eval, step, CryptoOracle.Interactive.ResponseLoading.fromCells]
  | cons bit left ih =>
      rw [show (bit :: left).length + 1 = (left.length + 1) + 1 by rfl, eval]
      simp only [step, List.map_cons, Tape.moveLeft, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem prepare_run (code : Program) (request : List Bool) :
    eval (step code) (3 * request.length + 3) (.loading request {}) =
      PMF.pure (.executing (.running (loaded request))) := by
  rw [show 3 * request.length + 3 =
    (2 * request.length + 1) + ((request.length + 1) + 1) by omega, eval_add]
  have hw := writing code request []
  simp only [List.reverse_nil, List.map_nil, List.nil_append] at hw
  rw [hw, PMF.pure_bind, eval_add]
  have hr := rewind code request.reverse none []
  simp only [List.length_reverse, List.reverse_reverse] at hr
  rw [hr, PMF.pure_bind]
  simp [eval, step, loaded, CryptoOracle.Interactive.ResponseLoading.loaded]

noncomputable def preparation (code : Program) (request : List Bool) :
    TimedExecution.Procedure (step code) Unit Unit :=
  TimedExecution.Procedure.ofFixed _ (fun _ => .loading request {})
    (fun _ _ => .executing (.running (loaded request))) (fun _ => PMF.pure ())
    (fun _ => 3 * request.length + 3)
    (fun _ => by simpa only [PMF.pure_map] using prepare_run code request)

private theorem append_blank (cells : List (Option Bool)) (i : Nat) :
    (cells ++ [none]).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => cases i <;> simp
  | cons cell rest ih =>
      cases i with
      | zero => rfl
      | succ i => simpa only [List.cons_append, List.getD_cons_succ] using ih i

/-- This proves the loader's represented final blank is harmless; no
transition removes that blank or replaces the actual loaded configuration. -/
theorem loaded_equivalent (request : List Bool) :
    (loaded request).Equivalent (Configuration.initial request).swapTapes := by
  refine ⟨rfl, rfl, Tape.Equivalent.refl _, ?_⟩
  cases request with
  | nil => exact Tape.Equivalent.refl _
  | cons bit rest =>
      refine ⟨rfl, fun _ => rfl, ?_⟩
      intro i
      exact append_blank (rest.map some) i

variable {Argument : Type u} {Result : Type v} (P : NativeComponent Argument Result)
    (request : List Bool) (argument : Argument)
    (hEntry : (loaded request).Equivalent (P.procedure.execution.entry argument))
    (cap : Nat)
    (hValid : ∀ result ∈ (P.procedure.execution.semantics argument).support,
      NativeCellResponse.Valid cap (P.procedure.execution.exit argument result))

noncomputable def native :=
  (NativeCellResponse.fromEquivalent P ⟨argument, loaded request, hEntry⟩ cap hValid).transport
    (step P.procedure.code) Control.executing (fun _ => rfl)

noncomputable def whole :=
  (preparation P.procedure.code request).seq (native P request argument hEntry cap hValid)
    (fun _ _ _ => rfl) (fun _ => P.procedure.execution.budget argument + (3 * cap + 4))
    (fun _ _ _ => Nat.le_refl _)

noncomputable def service :=
  (whole P request argument hEntry cap hValid).observe (fun result => result.2.2)
    (fun _ packet => .executing (.returned packet)) (fun _ _ _ => rfl)

theorem service_entry : (service P request argument hEntry cap hValid).entry () = .loading request {} := rfl

theorem service_exit (packet : List Bool) :
    (service P request argument hEntry cap hValid).exit () packet = .executing (.returned packet) := rfl

theorem service_budget : (service P request argument hEntry cap hValid).budget () =
    (3 * request.length + 3) + (P.procedure.execution.budget argument + (3 * cap + 4)) := rfl

/-- Loading and ownership handoff add their actual time to the native
first-halt and packet export time, preserving all correlations. -/
theorem service_costed : (service P request argument hEntry cap hValid).costed () =
    (P.firstArrival.procedure.execution.costed argument).map (fun result =>
      (result.1.outputBits, (3 * request.length + 3) +
        (result.2 + (3 * result.1.outputBits.length + 4)))) := by
  change (((preparation P.procedure.code request).costed ()).bind _).map _ = _
  simp only [preparation, TimedExecution.Procedure.ofFixed, PMF.pure_map, PMF.pure_bind, PMF.map_comp,
    Function.comp_def]
  have h := congrArg (fun distribution => distribution.map
    (fun result : List Bool × Nat => (result.1, (3 * request.length + 3) + result.2)))
    (NativeCellResponse.fromEquivalent_costed P ⟨argument, loaded request, hEntry⟩ cap hValid)
  simpa only [native, TimedExecution.Procedure.transport, PMF.map_comp, Function.comp_def] using h

theorem service_semantics : (service P request argument hEntry cap hValid).semantics () =
    (P.firstArrival.procedure.execution.semantics argument).map Configuration.outputBits := by
  have h := congrArg (fun distribution => distribution.map Prod.fst)
    (service_costed P request argument hEntry cap hValid)
  rw [(service P request argument hEntry cap hValid).correct] at h
  simp only [PMF.map_comp, Function.comp_def] at h
  have hc := congrArg (fun distribution => distribution.map Configuration.outputBits)
    (P.firstArrival.procedure.execution.correct argument)
  simp only [PMF.map_comp, Function.comp_def] at hc
  exact h.trans hc

include hEntry hValid in
theorem service_run (horizon : Nat)
    (hTime : (3 * request.length + 3) + (P.procedure.execution.budget argument + (3 * cap + 4)) ≤ horizon) :
    eval (step P.procedure.code) horizon (.loading request {}) =
      (P.firstArrival.procedure.execution.semantics argument).map
        (fun state => .executing (.returned state.outputBits)) := by
  have h := (service P request argument hEntry cap hValid).final_run ()
    (fun packet _ => by simp [service_exit, step, CellResponseExport.step, PMF.pure_map]) horizon hTime
  rw [service_entry, service_semantics, PMF.map_comp] at h
  exact h

end Machine.NativePacketService
