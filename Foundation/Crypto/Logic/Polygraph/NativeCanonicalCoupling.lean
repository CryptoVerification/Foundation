import Foundation.Crypto.Semantics.Machine.NativeCanonicalCouplingExecution
import Foundation.Crypto.Logic.Polygraph.ExperimentInterpretation

/-! Exact probabilistic game steps reify the verified native transformation.
The target includes an executed, charged terminal wrapper. Both full-cell
and public-output distributions agree. Arbitrary logical continuations do
not receive a native implementation or a runtime bound from this theorem. -/
namespace CryptoLogic.Polygraph.Experiment.NativeCanonicalCoupling
open Foundation.Probability
open Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
noncomputable section

def fullLaw (message : Bool) : PMF Machine.NativePreparedState.State :=
  (Machine.evalConfigWithin Machine.NativeCanonicalCouplingExecution.bounded.program
    (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput (sharpTableChain 0) message))
    (Machine.NativeCanonicalCouplingExecution.bounded.budget 39)).map Machine.NativePreparedState.state

def targetLaw (message : Bool) : PMF Machine.NativePreparedState.State :=
  (Machine.evalConfigWithin Machine.NativeCanonicalCouplingExecution.targetBounded.program
    (Machine.Configuration.initial (Machine.NativePreparedKeyDecision.rawInput (sharpTableChain 2) message))
    (Machine.NativeCanonicalCouplingExecution.targetBounded.budget 39)).map Machine.NativePreparedState.state

def nativeGame (message : Bool) : Program Machine.NativePreparedState.State := .sample (fullLaw message)
def targetGame (message : Bool) : Program Machine.NativePreparedState.State := .sample (targetLaw message)

theorem full_law_equal (message : Bool) : fullLaw message = targetLaw message :=
  Machine.NativeCanonicalCouplingExecution.full_cell_law_equal message

def fullReification (message : Bool) : ExactStep (nativeGame message) (targetGame message) :=
  .distribution (full_law_equal message)

def fullContextPath {A : Type} (message : Bool) (next : Machine.NativePreparedState.State → Program A) :
    ExactPath (.bind (nativeGame message) next) (.bind (targetGame message) next) :=
  .step (.bindFirst (fullReification message) next)

def publicGame (message : Bool) : Program (Option (List Bool)) :=
  .sample (Machine.evalWithin Machine.NativeCanonicalCouplingExecution.bounded.program
    (Machine.NativePreparedKeyDecision.rawInput (sharpTableChain 0) message)
    (Machine.NativeCanonicalCouplingExecution.bounded.budget 39))

def publicTargetGame (message : Bool) : Program (Option (List Bool)) :=
  .sample (Machine.evalWithin Machine.NativePreparedKeyDecision.bounded.program
    (Machine.NativePreparedKeyDecision.rawInput (sharpTableChain 2) message)
    (Machine.NativePreparedKeyDecision.bounded.budget 39))

def publicReification (message : Bool) : ExactStep (publicGame message) (publicTargetGame message) :=
  .distribution (Machine.NativeCanonicalCouplingExecution.public_reference_law_equal message)

def publicContextPath {A : Type} (message : Bool) (next : Option (List Bool) → Program A) :
    ExactPath (.bind (publicGame message) next) (.bind (publicTargetGame message) next) :=
  .step (.bindFirst (publicReification message) next)

end
end CryptoLogic.Polygraph.Experiment.NativeCanonicalCoupling
