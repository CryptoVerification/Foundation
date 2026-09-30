import Foundation.Machine.ProgramTransformation
import Foundation.Security.Reduction

universe u v a b c d

namespace Reduction

/-- The ordinary security transport specializes directly to machine-based
polynomial-time adversary classes. The transformation certificate supplies
the required admissibility preservation; the advantage loss remains a
separate assumption. -/
theorem secureOnWithin_machinePPT
    {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    (R : Reduction P Q)
    (JP : Machine.MachineAdversaryInterface.{u, a, b} P)
    (JQ : Machine.MachineAdversaryInterface.{v, c, d} Q)
    (F : InstanceFamily P)
    (T : R.MachineProgramTransformation JP JQ)
    (hLoss : R.loss.PreservesNegligible)
    (hSecure : SecureOnWithin Q JQ.pptClass (R.mapFamily F)) :
    SecureOnWithin P JP.pptClass F :=
  R.secureOnWithin JP.pptClass JQ.pptClass F
    T.preservesAdmissibility hLoss hSecure

end Reduction
