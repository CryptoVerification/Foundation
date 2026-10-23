import Foundation.Crypto.Logic.Polygraph.GameCoherenceRules
import Foundation.Crypto.Logic.Polygraph.GameCoherenceCertificate
import Foundation.Crypto.Logic.Polygraph.GameCoherenceDiagram

/-! Concrete tests of the directed stochastic interpretation. The positive
error example is a fair-bit replacement, not an exact rewrite. The obstruction
shows why equal endpoint laws cannot certify a higher comparison. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Examples
open Foundation.Probability Foundation.Logic.Polygraph
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

def fairWin : Observed := ⟨Bool, .sample (uniform Bool), (· = true)⟩
def lose : Observed := ⟨Bool, .pure false, (· = true)⟩

def replaceBit : Step fairWin lose where
  kernel _ := PMF.pure false
  preserve := PMF.bind_const _ _
  bad pair := pair.1 = true
  agree x _ y reachable good := by
    have same := (PMF.mem_support_pure_iff false y).mp reachable
    subst y
    exact iff_of_false good (by change ¬((false : Bool) = true); decide)
  loss := 1 / 2
  bound := by
    change eventProb ((uniform Bool).bind fun x =>
      (PMF.pure false).map (fun y => (x, y))) (fun pair => pair.1 = true) ≤ 1 / 2
    simp only [PMF.pure_map]
    change eventProb ((uniform Bool).map (fun x => (x, false))) _ ≤ _
    rw [eventProb_map]
    exact le_of_eq (by simpa using uniform_guess true)

def replacement : Path fairWin lose := .step replaceBit

theorem replacement_loss : replacement.loss = 1 / 2 := rfl

theorem replacement_gap : probabilityGap fairWin.probability lose.probability = 1 / 2 := by
  have fair : fairWin.probability = 1 / 2 := by
    simpa [fairWin, Observed.probability, Program.eval] using uniform_guess true
  have lost : lose.probability = 0 := by simp [lose, Observed.probability, Program.eval, eventProb]
  rw [fair, lost]
  simp [probabilityGap]

def positiveExchange : Cell4
    (.seq (replacement.left fairWin) (replacement.right lose))
    (.seq (replacement.right fairWin) (replacement.left lose)) :=
  Cell4.exchange replacement replacement

theorem positive_exchange_loss :
    (Path.seq (replacement.left fairWin) (replacement.right lose)).loss = 1 := by
  simp only [Path.loss, Path.left_loss, Path.right_loss, replacement_loss]
  rw [← two_mul]
  simpa only [one_div] using
    ENNReal.mul_inv_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)

def sampleThenErase : Cell4
    (.seq (.step (sample fairWin (uniform Bool))) (.step (eraseSample fairWin (uniform Bool))))
    (.identity fairWin) := sampleErase _ _

def copyThenErase : Cell4
    (.seq (.step (copy fairWin)) (.step (eraseCopy fairWin))) (.identity fairWin) := copyErase _

/-- Retain both sampled bits while exchanging their execution order. -/
def sampleExchange (p q : PMF Bool) : ExactPath
    (.bind (.sample p) (fun a => .bind (.sample q) (fun b => .pure (a, b))))
    (.bind (.sample q) (fun b => .bind (.sample p) (fun a => .pure (a, b)))) :=
  .step (.independent p q (fun a b => .pure (a, b)))

def sampleExchangeRoutes (p q : PMF Bool) : Cell4
    (.step (Step.exact (sampleExchange p q) (fun pair => pair.1 = pair.2)))
    (.step (Step.exact (.comp (.refl _) (sampleExchange p q)) (fun pair => pair.1 = pair.2))) :=
  exactRoutes _ _ _

def fairState : Observed := privateGame (uniform Bool)

def flipBit : Step fairState fairState :=
  Step.ofMap _ _ Bool.not
    (uniform_map_equiv ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩)
    (fun _ _ => Iff.rfl)

/-- Both paths preserve the very same fair endpoint law, but their conditional
state correspondences differ. A four-cell cannot be fabricated from marginals. -/
theorem no_identity_flip_comparison :
    ¬Nonempty (Cell4 (.identity fairState) (.step flipBit)) := by
  rintro ⟨cell⟩
  have impossible : (true : Bool) = false :=
    cell.deterministic_output id true true false (PMF.pure_map _ _) (PMF.pure_map _ _)
  cases impossible

/-- A raw diagram structural edit followed by a genuinely probabilistic edit.
The result still records the conditional kernel and exact loss. -/
def mixedEdits : DiagramBridge.Edits
    (.seq (.identity _) (DiagramBridge.diagram
      (.seq (.step (sample fairWin (uniform Bool))) (.step (eraseSample fairWin (uniform Bool))))))
    (DiagramBridge.diagram (.identity fairWin)) :=
  .comp (.step (.structural (.step (.leftUnit _))))
    (.step (.game (by
      simpa only [DiagramBridge.evaluate_diagram] using sampleThenErase)))

theorem mixed_kernel (state : fairWin.Outcome) :
    (DiagramBridge.evaluate
      (.seq (.identity _) (DiagramBridge.diagram
        (.seq (.step (sample fairWin (uniform Bool))) (.step (eraseSample fairWin (uniform Bool))))))).kernel state =
      PMF.pure state := by
  exact DiagramBridge.edited_kernel mixedEdits state

/-- Reuse any actual backend execution certificate; no fabricated machine
model, runtime estimate or code equivalence assumption is introduced. -/
def certifiedExchange {K : General.CodeSystem} {m n : K.Machine}
    {X : General.SecurityObject.{0, 0} K m} {Y : General.SecurityObject.{0, 0} K n}
    (reduction : General.CertifiedReduction X Y) (F A) (W : X.Witness F A) :
    Cell4 (Certified.gameFirst reduction F A W replacement)
      (Certified.reductionFirst reduction F A W replacement) :=
  Certified.interchange reduction F A W replacement

theorem certified_loss {K : General.CodeSystem} {m n : K.Machine}
    {X : General.SecurityObject.{0, 0} K m} {Y : General.SecurityObject.{0, 0} K n}
    (reduction : General.CertifiedReduction X Y) (F A) (W : X.Witness F A) :
    (Certified.reductionFirst reduction F A W replacement).loss = 1 / 2 :=
  (Certified.loss_preserved reduction F A W replacement).2

end
end CryptoLogic.Polygraph.Experiment.GameCoherence.Examples
