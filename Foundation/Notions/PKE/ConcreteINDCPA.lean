import Foundation.Notions.PKE.INDCPA
import Foundation.Probability.Comp

open Foundation.Probability
open scoped ENNReal

/-- The concrete left-or-right IND-CPA experiment for probabilistic `PKE`.
`keygen`, `choose`, `encrypt`, and `guess` are PMF computations; each bind
uses fresh random coins. `false` selects the first message and `true` the
second. The current PKE interface has one message type and no length field. -/
noncomputable def indCPAExperiment (scheme : PKE ProbComp)
    (A : INDCPAAdversary ProbComp scheme) : ProbComp Bool :=
  scheme.keygen.bind fun (pk, _sk) =>
    (A.choose pk).bind fun (m₀, m₁, state) =>
      sampleBit.bind fun β =>
        (scheme.encrypt pk (if β then m₁ else m₀)).bind fun ciphertext =>
          (A.guess state ciphertext).bind fun guess =>
            PMF.pure (guess == β)

noncomputable def indCPASuccessProb (scheme : PKE ProbComp)
    (A : INDCPAAdversary ProbComp scheme) : ℝ≥0∞ :=
  eventProb (indCPAExperiment scheme A) (· = true)

/-- The Phase 11a guessing convention: `|Pr[win] - 1/2|`. -/
noncomputable def indCPAAdvantage (scheme : PKE ProbComp)
    (A : INDCPAAdversary ProbComp scheme) : ℝ≥0∞ :=
  guessingAdvantage (indCPASuccessProb scheme A)

/-- Concrete PMF semantics for the existing IND-CPA goal. -/
noncomputable def concreteINDCPASemantics : INDCPASemantics ProbComp where
  advantage _ scheme A := indCPAAdvantage scheme A
