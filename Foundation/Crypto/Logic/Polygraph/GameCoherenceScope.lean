import Foundation.Crypto.Logic.Polygraph.GameCoherenceCertificate
import Foundation.Crypto.Logic.Polygraph.GameCoherenceDiagram

/-! Scope checks for research claims about the stochastic game layer.
These facts expose what its current interfaces do and do not establish:
arbitrary semantic equality is an allowed four-cell generator; witness-register
exchange is an instance of ordinary independent interchange; and elimination
of every successful outcome is equivalent to supplying the success bound.
These are interface audits, not claims of new mathematical results. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Scope
open Foundation.Probability
open scoped ENNReal
universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- This is not completeness for a restricted syntactic list of local rules:
the reverse implication directly invokes the unrestricted semantic generator. -/
theorem cell_iff_comparison {a b : Observed.{u}} (p q : Path a b) :
    Nonempty (Cell4 p q) ↔ Comparison p q :=
  ⟨fun ⟨cell⟩ => cell.sound, fun comparison => ⟨.generator comparison⟩⟩

theorem cell_iff_kernel_loss {a b : Observed.{u}} (p q : Path a b) :
    Nonempty (Cell4 p q) ↔ (∀ state, p.kernel state = q.kernel state) ∧ p.loss = q.loss := by
  rw [cell_iff_comparison]
  exact ⟨fun comparison => ⟨comparison.kernel_eq, comparison.loss_eq⟩,
    fun ⟨kernel, loss⟩ => ⟨kernel, loss⟩⟩

/-- Mixing raw structural edits into this layer does not restrict the
semantic generator or establish a finite stochastic homotopy basis. -/
theorem edits_iff_comparison {a b : Observed} (d e : DiagramBridge.Closed a b) :
    Nonempty (DiagramBridge.Edits d e) ↔
      Comparison (DiagramBridge.evaluate d) (DiagramBridge.evaluate e) :=
  ⟨fun ⟨edits⟩ => (DiagramBridge.edit_comparison edits).sound,
    fun comparison => ⟨.step (.game (.generator comparison))⟩⟩

/-- No cryptographic hypothesis is needed for this register exchange. -/
def registerExchange {A B : Type u} (f : A → B) (value : A)
    {first last : Observed.{u}} (path : Path first last) : Cell4
    (path.parallel (.step (constantMap f value)))
    (.seq ((Path.step (constantMap f value)).right first)
      (path.left (constantGame (f value)))) :=
  Cell4.exchange path (.step (constantMap f value))

theorem certified_exchange_specializes {K : General.CodeSystem} {m n : K.Machine}
    {X : General.SecurityObject.{0, 0} K m} {Y : General.SecurityObject.{0, 0} K n}
    (reduction : General.CertifiedReduction X Y) (F A) (W : X.Witness F A)
    {first last : Observed.{0}} (path : Path first last) :
    Certified.interchange reduction F A W path =
      registerExchange (reduction.mapWitness F A) W path := rfl

def losingGame : Observed.{u} := ⟨ULift.{u} Unit, .pure ⟨()⟩, fun _ => False⟩

theorem losing_probability : losingGame.probability = 0 := by
  simp [losingGame, Observed.probability, eventProb]

/-- The success bound is an input to this transformation. This construction
alone cannot serve as an independent proof of that same bound. -/
def eliminate (game : Observed.{u}) (error : ℝ≥0∞) (bound : game.probability ≤ error) :
    Step game losingGame where
  kernel _ := PMF.pure ⟨()⟩
  preserve := PMF.bind_const _ _
  bad pair := game.event pair.1
  agree _ _ _ _ good := iff_of_false good id
  loss := error
  bound := by
    change eventProb (game.program.eval.bind fun x =>
      (PMF.pure (ULift.up () : ULift.{u} Unit)).map (fun y => (x, y)))
      (fun pair => game.event pair.1) ≤ _
    simp only [PMF.pure_map]
    change eventProb (game.program.eval.map (fun x => (x, ULift.up ()))) _ ≤ _
    rw [eventProb_map]
    exact bound

theorem elimination_iff_bound (game : Observed.{u}) (error : ℝ≥0∞) :
    (∃ transition : Step game losingGame, transition.loss = error) ↔ game.probability ≤ error := by
  constructor
  · rintro ⟨transition, loss⟩
    have sound := transition.hop.sound
    rw [losing_probability, loss] at sound
    simp only [probabilityGap, tsub_zero, zero_tsub] at sound
    exact (le_max_left _ _).trans sound
  · intro bound
    exact ⟨eliminate game error bound, rfl⟩

end
end CryptoLogic.Polygraph.Experiment.GameCoherence.Scope
