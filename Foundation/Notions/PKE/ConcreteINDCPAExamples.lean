import Foundation.Notions.PKE.ConcreteINDCPA

namespace ConcreteINDCPAExamples

open Foundation.Probability

/-- A deliberately revealing toy scheme for experiment sanity checks. -/
noncomputable def leakyScheme : PKE ProbComp where
  PublicKey := Unit
  SecretKey := Unit
  Message := Bool
  Ciphertext := Bool
  keygen := PMF.pure ((), ())
  encrypt := fun _ message => PMF.pure message
  decrypt := fun _ ciphertext => some ciphertext

noncomputable def leakyAdversary : INDCPAAdversary ProbComp leakyScheme where
  State := Unit
  choose := fun _ => PMF.pure (false, true, ())
  guess := fun _ ciphertext => PMF.pure ciphertext

example : indCPAExperiment leakyScheme leakyAdversary = PMF.pure true := by
  rw [indCPAExperiment]
  simp [leakyScheme, leakyAdversary, PMF.pure_bind]

example : indCPASuccessProb leakyScheme leakyAdversary = 1 := by
  rw [indCPASuccessProb]
  have h : indCPAExperiment leakyScheme leakyAdversary = PMF.pure true := by
    rw [indCPAExperiment]
    simp [leakyScheme, leakyAdversary, PMF.pure_bind]
  rw [h]
  simp [eventProb]

example : indCPAAdvantage leakyScheme leakyAdversary = 1 / 2 := by
  have h : indCPASuccessProb leakyScheme leakyAdversary = 1 := by
    rw [indCPASuccessProb]
    have hg : indCPAExperiment leakyScheme leakyAdversary = PMF.pure true := by
      rw [indCPAExperiment]
      simp [leakyScheme, leakyAdversary, PMF.pure_bind]
    rw [hg]
    simp [eventProb]
  simp [indCPAAdvantage, guessingAdvantage, probabilityGap, h]

noncomputable example : CryptoGoal := INDCPA ProbComp concreteINDCPASemantics

end ConcreteINDCPAExamples
