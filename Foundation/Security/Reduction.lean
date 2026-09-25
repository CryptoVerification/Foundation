import Foundation.Resource.Reduction
import Foundation.Asymptotics.AdvantageBound
import Foundation.Security.Asymptotic

universe u v

namespace Reduction

/-- A reduction from `P` to `Q` transports asymptotic security from `Q` to
`P`, provided the transformed adversary family remains admissible and the
advantage loss preserves negligibility. -/
theorem secureOnWithin {P : CryptoGoal.{u}} {Q : CryptoGoal.{v}}
    (R : Reduction P Q) (CP : AdversaryClass P)
    (CQ : AdversaryClass Q) (F : InstanceFamily P)
    (hAdm : R.PreservesAdmissibility CP CQ)
    (hLoss : R.loss.PreservesNegligible)
    (hSecure : SecureOnWithin Q CQ (R.mapFamily F)) :
    SecureOnWithin P CP F := by
  intro A hA
  have hMapped : CQ.admissible (R.mapFamily F) (R.mapAdversaryFamily F A) :=
    hAdm.preserves F A hA
  have hTarget : Negligible
      (advantageProfile Q (R.mapFamily F) (R.mapAdversaryFamily F A)) :=
    hSecure (R.mapAdversaryFamily F A) hMapped
  have hLossed : Negligible
      (fun n => R.loss.eval n
        (advantageProfile Q (R.mapFamily F) (R.mapAdversaryFamily F A) n)) :=
    hLoss _ hTarget
  exact Negligible.mono (R.advantageProfile_le F A) hLossed

end Reduction
