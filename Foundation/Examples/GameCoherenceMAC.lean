import Foundation.Examples.GameCoherence
import Foundation.Examples.ScheduleCertificate

/-! Apply the stochastic interpretation to an adaptive MAC attack. Exact
schedule changes retain the secret function, applied set, full oracle trace
and verification result. Eliminating a forgery is a distinct statistical step
with positive error, certified by the existing ideal-MAC theorem. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC
open Foundation.Probability Foundation.Logic.Polygraph
open Foundation.Logic.Polygraph.ScheduleCertificate
open Foundation.Symmetric.RandomFunctionMACSchedules
open CryptoOracle.RandomOracle
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev FullOutcome := CryptoOracle.Outcome (Fin 8) (Fin 256) Bool
  (Finset (Fin 8) × (Fin 8 → Fin 256))

def fullLaw (schedule : Schedule 8) : PMF FullOutcome :=
  (uniform (Fin 8 → Fin 256)).bind fun key =>
    ((checkedAttack [] Foundation.Symmetric.RandomFunctionMACSchedules.Examples.attack).run
      Cube.coordinateOracle ((localCertificate 8 (Fin 256)).toCube.run (order schedule) (∅, key)))

def fullGame (schedule : Schedule 8) : Observed :=
  ⟨FullOutcome, .sample (fullLaw schedule), fun outcome => outcome.result = true⟩

theorem full_law_eq (first second : Schedule 8) : fullLaw first = fullLaw second := by
  unfold fullLaw
  simp_rw [scheduled_state]

theorem full_security (schedule : Schedule 8) : (fullGame schedule).probability ≤ (256 : ℝ≥0∞)⁻¹ := by
  have projected := Foundation.Symmetric.RandomFunctionMACSchedules.Examples.forgery_bound schedule
  rw [scheduledGame, ← PMF.map_bind, eventProb_map] at projected
  exact projected

def schedulePath (first second : Schedule 8) : Path (fullGame first) (fullGame second) :=
  .step (Step.exact (.step (.distribution (full_law_eq first second))) (fun out => out.result = true))

theorem schedule_kernel (first second : Schedule 8) (state : FullOutcome) :
    (schedulePath first second).kernel state = PMF.pure state := rfl

theorem schedule_loss (first second : Schedule 8) : (schedulePath first second).loss = 0 := rfl

/-- Full state and trace laws, not just success probabilities, agree when
comparing a direct schedule change with a two-stage change. -/
def scheduleTriangle (first middle last : Schedule 8) : Cell4
    (.seq (schedulePath first middle) (schedulePath middle last)) (schedulePath first last) :=
  .generator ⟨by
    intro state
    simp only [Path.kernel, schedule_kernel, PMF.pure_bind], by
    simp only [Path.loss, schedule_loss, add_zero]⟩

def noForgery : Observed := ⟨Unit, .pure (), fun _ => False⟩

def eliminateForgery (schedule : Schedule 8) : Step (fullGame schedule) noForgery where
  kernel _ := PMF.pure ()
  preserve := PMF.bind_const _ _
  bad pair := pair.1.result = true
  agree _ _ _ _ good := iff_of_false good id
  loss := (256 : ℝ≥0∞)⁻¹
  bound := by
    change eventProb ((fullLaw schedule).bind fun x =>
      (PMF.pure ()).map (fun y => (x, y))) (fun pair => pair.1.result = true) ≤ _
    simp only [PMF.pure_map]
    change eventProb ((fullLaw schedule).map (fun x => (x, ()))) _ ≤ _
    rw [eventProb_map]
    exact full_security schedule

/-- Reordering two independent forgery-elimination steps is valid even though
both steps have positive statistical error and erase their state. -/
def statisticalExchange (first second : Schedule 8) : Cell4
    (.seq ((Path.step (eliminateForgery first)).left (fullGame second))
      ((Path.step (eliminateForgery second)).right noForgery))
    (.seq ((Path.step (eliminateForgery second)).right (fullGame first))
      ((Path.step (eliminateForgery first)).left noForgery)) :=
  Cell4.exchange _ _

theorem elimination_disagreement (schedule : Schedule 8) :
    eventProb (Path.step (eliminateForgery schedule)).joint
      (mismatch (fullGame schedule) noForgery) ≤ (256 : ℝ≥0∞)⁻¹ :=
  (Path.step (eliminateForgery schedule)).mismatch_bound

end
end CryptoLogic.Polygraph.Experiment.GameCoherence.Examples.MAC
