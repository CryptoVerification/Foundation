import Foundation.Core.SecurityBound
import Foundation.Constructions.ElGamal.Basic
import Foundation.Notions.PKE.INDCPA

open scoped ENNReal

/-- Generic IND-CPA restricted to ElGamal construction instances.
This introduces no new attack notion or experiment semantics. -/
def ElGamalINDCPA (M : Type → Type) (S : INDCPASemantics M) : CryptoGoal :=
  (INDCPA M S).reindex (fun _ => ElGamalInstance M) (fun _ I => I.scheme)

/-- Specialization of `CryptoGoal.boundedByOn_reindex_iff` to ElGamal schemes. -/
theorem elGamalINDCPA_boundedByOn_iff (M : Type → Type)
    (S : INDCPASemantics M) (F : InstanceFamily (ElGamalINDCPA M S))
    (ε : Nat → ℝ≥0∞) :
    BoundedByOn (ElGamalINDCPA M S) F ε ↔
      BoundedByOn (INDCPA M S) (fun n => (F n).scheme) ε := by
  exact CryptoGoal.boundedByOn_reindex_iff (INDCPA M S)
    (fun _ => ElGamalInstance M) (fun _ I => I.scheme) F ε
