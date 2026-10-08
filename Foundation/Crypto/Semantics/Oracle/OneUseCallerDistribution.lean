import Foundation.Crypto.Semantics.Oracle.OneUseCallerStopping
import Foundation.Crypto.Semantics.ProcedureStage

/-! Exact distributional correspondence between the caller's logical query
operations and ordinary/query round composition. Logical instruction costs
are kept separate from the native controller's request/response costs. -/
namespace CryptoOracle.Interactive.OneUseSourceRounds
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
variable {State : Type u} (code : Code) (oracle : BitOracle State)
    (key : List Bool) (keyTail : List (Option Bool))

theorem query_run (source : Boundary State) :
    TimedExecution.eval (callerStep code oracle key keyTail) (queryOperations code source) source =
      (query code oracle key keyTail).semantics source := by
  cases hb : OneUseSourceInterval.boundary code source.frame.control with
  | true => simp [queryOperations, callerStep, hb, TimedExecution.eval, PMF.bind_pure]
  | false =>
      change _ = (queryAt code oracle key keyTail source).semantics ()
      rw [queryAt_before_boundary code oracle key keyTail source hb]
      simp [queryOperations, hb, TimedExecution.eval]

noncomputable def queryAnalysisAt (source : Boundary State) :=
  Procedure.ofFixed (callerStep code oracle key keyTail) (fun _ : Unit => source) (fun _ result => result)
    (fun _ => (query code oracle key keyTail).semantics source) (fun _ => queryOperations code source)
    (fun _ => by rw [query_run]; exact (PMF.map_id _).symm)

noncomputable def callerAnalysisAt (fuel : Nat) (source : Boundary State) :=
  ((Procedure.interval (Reification.timedStep code oracle) (callerStep code oracle key keyTail)
    (fun frame => OneUseSourceInterval.boundary code frame.control)
    (fun source => OneUseSourceInterval.boundary code source.frame.control) (Boundary.mk source.spent)
    (fun _ => rfl) (fun frame hb => by simp [callerStep, hb]) fuel).reindex (fun _ : Unit => source.frame)).observe
    (Boundary.mk source.spent) (fun _ result => result) (fun _ _ _ => rfl)

noncomputable def roundAnalysis (fuel : Nat) :=
  ((Procedure.dispatch (callerAnalysisAt code oracle key keyTail fuel)).seq
    (Procedure.dispatch (queryAnalysisAt code oracle key keyTail)) (fun _ _ _ => rfl)
    (fun _ => 1) (fun _ middle _ => by
      change queryOperations code middle ≤ 1
      unfold queryOperations
      split <;> omega)).observe Prod.snd (fun _ result => result) (fun _ _ _ => rfl)

theorem roundAnalysis_semantics (stateSize : State → Nat) (fuel : Nat) (source : Boundary State) :
    (roundAnalysis code oracle key keyTail fuel).semantics source =
      (automaticRound stateSize code oracle key keyTail fuel).semantics source := by
  rw [automaticRound_semantics]
  simp only [roundAnalysis, Procedure.observe, Procedure.seq, PMF.map_bind, PMF.map_comp, Function.comp_def]
  congr 1
  funext middle
  exact PMF.map_id _

theorem caller_distribution (stateSize : State → Nat) (fuel : Nat) (hFuel : 0 < fuel)
    (start : Boundary State) (bound count : Nat) (hCount : bound ≤ count)
    (hStop : ∀ final ∈ (TimedExecution.eval (callerStep code oracle key keyTail) bound start).support,
      Reification.terminal final.frame.control = true) :
    TimedExecution.eval (callerStep code oracle key keyTail) bound start =
      TimedExecution.eval (automaticRound stateSize code oracle key keyTail fuel).semantics count start := by
  have hSem : (roundAnalysis code oracle key keyTail fuel).semantics =
      (automaticRound stateSize code oracle key keyTail fuel).semantics :=
    funext (roundAnalysis_semantics code oracle key keyTail stateSize fuel)
  have hFinal : ∀ final ∈ (TimedExecution.eval
      (roundAnalysis code oracle key keyTail fuel).semantics count start).support,
      callerStep code oracle key keyTail final = PMF.pure final := by
    intro final hs
    apply callerStep_terminal code oracle key keyTail final
    apply automatic_stops_of_caller stateSize code oracle key keyTail fuel hFuel start bound count hCount hStop final
    rwa [hSem] at hs
  have hRun := Stage.iterateProcedure_final (roundAnalysis code oracle key keyTail fuel)
    (embed := id) (fun _ => rfl) (fun _ _ => rfl) (fuel + 1) (fun _ => Nat.le_refl _) count start hFinal
    (count * (fuel + 1)) (Nat.le_refl _)
  simp only [id_eq] at hRun
  have hHorizon : bound ≤ count * (fuel + 1) := by nlinarith
  rw [terminal_stable (callerStep code oracle key keyTail) (fun source => Reification.terminal source.frame.control)
    (callerStep_terminal code oracle key keyTail) start bound hStop (count * (fuel + 1)) hHorizon,
    PMF.map_id, hSem] at hRun
  exact hRun

variable (stateSize : State → Nat) (callerFrame : Configuration State)
    (fuel : Nat) (hFuel : 0 < fuel) (predicate : Boundary State → Prop)
    (hClosed : ∀ source, predicate source →
      ∀ result ∈ ((automaticRound stateSize code oracle key keyTail fuel).semantics source).support, predicate result)
    (hInitial : predicate ⟨false, callerFrame⟩) (bound count : Nat) (hCount : bound ≤ count)
    (hStop : ∀ final ∈ (TimedExecution.eval (callerStep code oracle key keyTail) bound ⟨false, callerFrame⟩).support,
      Reification.terminal final.frame.control = true)
    (extentCap : Nat)
    (hExtent : ∀ source, predicate source → ControllerExtent.sourceExtent stateSize
      (embed (Machine.PairPreparation.operand [] key keyTail) source) ≤ extentCap)

include hFuel hClosed hInitial hCount hStop hExtent in
/-- Exact caller-level/physical-machine correspondence. The right-hand
logical clock counts queries once; the left-hand horizon includes real
capture, preparation, native computation, tagging and response loading. -/
theorem caller_machine_run (horizon : Nat)
    (hBudget : count * (fuel + (33 * (key.length + extentCap + fuel * 2) + 33)) ≤ horizon) :
    TimedExecution.eval (OneUseSource.step Machine.OneTimePad.Prepared.listProcedure.code code oracle)
      horizon (embed (Machine.PairPreparation.operand [] key keyTail) ⟨false, callerFrame⟩) =
      (TimedExecution.eval (callerStep code oracle key keyTail) bound ⟨false, callerFrame⟩).map
        (embed (Machine.PairPreparation.operand [] key keyTail)) := by
  let C := AutomaticCertificate.ofCallerStop stateSize code oracle key keyTail callerFrame fuel hFuel
    predicate hClosed hInitial bound count hCount hStop extentCap hExtent
  have h := OneUseSourceRounds.run code oracle key keyTail C.certificate.fuel C.certificate.cap
    C.certificate.capProof C.certificate.predicate C.certificate.closed C.certificate.bound C.certificate.bounded
    C.certificate.count C.certificate.start C.certificate.stops horizon (by
      simpa only [C, AutomaticCertificate.ofCallerStop, AutomaticCertificate.certificate] using hBudget)
  change TimedExecution.eval _ horizon (embed (Machine.PairPreparation.operand [] key keyTail) ⟨false, callerFrame⟩) =
    (TimedExecution.eval (automaticRound stateSize code oracle key keyTail fuel).semantics count ⟨false, callerFrame⟩).map
      (embed (Machine.PairPreparation.operand [] key keyTail)) at h
  rw [← caller_distribution code oracle key keyTail stateSize fuel hFuel ⟨false, callerFrame⟩ bound count hCount hStop] at h
  exact h

end CryptoOracle.Interactive.OneUseSourceRounds
