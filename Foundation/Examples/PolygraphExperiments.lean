import Foundation.Crypto.Meta.Polygraph.UniformHybrid
import Foundation.Constructions.Symmetric.EncryptThenMAC.Polygraph
import Foundation.Constructions.Symmetric.PRGPolygraphPaths
import Foundation.Crypto.Logic.Polygraph.ExperimentInterpretation

/-! Exact, statistical, computational, and hybrid interfaces are exercised
separately. In particular an exact rewrite cannot be fabricated from a positive
statistical error, and a code compiler cannot be supplied as a security proof. -/
namespace CryptoLogic.Polygraph.Examples

open Foundation.Probability Foundation.Logic.Polygraph
open scoped ENNReal

noncomputable def trueGame : Experiment.Observed := ⟨Bool, .pure true, (· = true)⟩
noncomputable def falseGame : Experiment.Observed := ⟨Bool, .pure false, (· = true)⟩

noncomputable def failureHop : Experiment.Hop trueGame falseGame 1 := by
  have h : eventProb (PMF.pure ()) (fun _ : Unit => True) = 1 := by simp [eventProb]
  exact h ▸ Experiment.Hop.coupling (PMF.pure ()) (fun _ => true) (fun _ => false)
    (by exact PMF.pure_map _ _)
    (by exact PMF.pure_map _ _) (fun _ => True)
    (fun _ _ hn => False.elim (hn trivial))

example : probabilityGap trueGame.probability falseGame.probability ≤ 1 := failureHop.sound

noncomputable def relaxed : Experiment.Hop trueGame falseGame 2 := failureHop.weaken (by norm_num)

example : probabilityGap trueGame.probability falseGame.probability ≤ 2 := relaxed.sound

example : probabilityGap trueGame.probability falseGame.probability ≤ 2 :=
  Experiment.Statistical.sound relaxed

noncomputable def swapSamples (p q : PMF Bool) : Experiment.ExactPath
    (.bind (.sample p) (fun a => .bind (.sample q) (fun b => .pure (a, b))))
    (.bind (.sample q) (fun b => .bind (.sample p) (fun a => .pure (a, b)))) :=
  .step (.independent p q (fun a b => .pure (a, b)))

example (p q : PMF Bool) :
    (Experiment.Program.bind (.sample p) (fun a => .bind (.sample q) (fun b => .pure (a, b)))).eval =
    (Experiment.Program.bind (.sample q) (fun b => .bind (.sample p) (fun a => .pure (a, b)))).eval :=
  (swapSamples p q).sound

-- Output code order comes from the pure diagram, without any game argument.
/-- info: [0, 1, 2, 3] -/
#guard_msgs in
#eval (Derivation.run (FiniteHybrid.proof 3) ([.halt])).map Prod.fst

example (games : Nat → ThreeGames.Game) (ε : Fin 4 → Nat → ℝ≥0∞) (n : Nat) :
    (Derivation.loss (FiniteHybrid.interpretation games) (FiniteHybrid.proof 3)).eval ε n =
      ∑ i, ε i n := FiniteHybrid.loss games 3 ε n

example (ε δ : ℝ≥0∞) :
    (Foundation.Symmetric.EncryptThenMAC.Polygraph.expand
      Foundation.Symmetric.EncryptThenMAC.Polygraph.proof).eval
        Foundation.Symmetric.EncryptThenMAC.Polygraph.lowerLoss
        (Fin.cases ε (fun _ => δ)) 0 = ε + δ :=
  Foundation.Symmetric.EncryptThenMAC.Polygraph.proof_loss ε δ

#guard_msgs (drop info) in
#check_failure (failureHop : Experiment.ExactPath trueGame.program falseGame.program)

end CryptoLogic.Polygraph.Examples
