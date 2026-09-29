import Foundation.Assumptions.DDH.DDH
import Foundation.Probability.Comp

open Foundation.Probability
open scoped ENNReal

/-- Finite, nonempty scalar sampling data, kept separate from DDH algebra. -/
structure DDHFiniteSampling (params : DDHParameters) where
  scalarFintype : Fintype params.Scalar
  scalarNonempty : Nonempty params.Scalar

namespace DDHFiniteSampling

/-- Uniformly sample a scalar from the supplied finite scalar type. -/
noncomputable def sampleScalar {params : DDHParameters}
    (S : DDHFiniteSampling params) : ProbComp params.Scalar := by
  letI := S.scalarFintype
  letI := S.scalarNonempty
  exact uniform params.Scalar

end DDHFiniteSampling

/-- The real DDH branch samples `x,y` and passes `(g^x,g^y,g^(xy))` to the
existing distinguisher. -/
noncomputable def ddhRealGame (params : DDHParameters) (S : DDHFiniteSampling params)
    (A : DDHAdversary ProbComp params) : ProbComp Bool :=
  S.sampleScalar.bind fun x => S.sampleScalar.bind fun y =>
    A.distinguish (params.power params.generator x)
    (params.power params.generator y)
    (params.power params.generator (params.mulScalar x y))

/-- The random DDH branch uses an independent third scalar `z`. -/
noncomputable def ddhRandomGame (params : DDHParameters) (S : DDHFiniteSampling params)
    (A : DDHAdversary ProbComp params) : ProbComp Bool :=
  S.sampleScalar.bind fun x => S.sampleScalar.bind fun y => S.sampleScalar.bind fun z =>
    A.distinguish (params.power params.generator x)
    (params.power params.generator y)
    (params.power params.generator z)

/-- A fair bit selects the real (`true`) or random (`false`) DDH branch. -/
noncomputable def ddhExperiment (params : DDHParameters) (S : DDHFiniteSampling params)
    (A : DDHAdversary ProbComp params) : ProbComp Bool :=
  sampleBit.bind fun β =>
    (if β then ddhRealGame params S A else ddhRandomGame params S A).bind fun guess =>
      PMF.pure (guess == β)

noncomputable def ddhSuccessProb (params : DDHParameters) (S : DDHFiniteSampling params)
    (A : DDHAdversary ProbComp params) : ℝ≥0∞ :=
  eventProb (ddhExperiment params S A) (· = true)

/-- DDH distinguishing advantage is the absolute gap between the two output
probabilities. This is the probability-gap convention of Phase 11a. -/
noncomputable def ddhAdvantage (params : DDHParameters) (S : DDHFiniteSampling params)
    (A : DDHAdversary ProbComp params) : ℝ≥0∞ :=
  probabilityGap
    (eventProb (ddhRealGame params S A) (· = true))
    (eventProb (ddhRandomGame params S A) (· = true))

/-- `DDHSemantics` is total on all algebraic parameters, including types with
no possible uniform scalar sampler. `none` is outside the finite experiment's
domain and receives zero advantage; theorems about an actual experiment use a
`some` sampling witness. -/
noncomputable def concreteDDHSemantics
    (sampling : (n : Nat) → (params : DDHParameters) → Option (DDHFiniteSampling params)) :
    DDHSemantics ProbComp where
  advantage n params A :=
    match sampling n params with
    | some S => ddhAdvantage params S A
    | none => 0
