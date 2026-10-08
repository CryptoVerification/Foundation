import Foundation.Constructions.Symmetric.PRGNativeQueryBackend

/-! Security transfer through actual registered query reductions. Every
witness has the same fixed finite code, public context and operational
runtime with polynomial time, one query and whole-prefix encoded memory.
Concrete PRG security and encryption-side evaluation remain premises. -/
namespace Foundation.Symmetric.PRGNativeQuerySecurity
open Machine Foundation.Probability TimedExecution CryptoLogic.General
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
variable {G : Generator} {Input : Type*} (I : PRGNativePipeline.Implementation G Input)
    (O : PolynomialObserver) (messages : InstanceFamily G.prgGoal)
    (hWidth : PolynomiallyBounded G.outputLength)

include hWidth in
theorem advantage_le (n : Nat) :
    probabilityGap (eventProb (PRGNativePipeline.game I O n (messages n).1) (· = true))
      (eventProb (PRGNativePipeline.game I O n (messages n).2) (· = true)) ≤
    (PRGNativeQueryBackend.registration G).nativeAdvantage messages (PRGNativeReductionConcrete.fixedCode O)
      (PRGNativeQueryBackend.witness G O false messages hWidth).resources n +
    (PRGNativeQueryBackend.registration G).nativeAdvantage messages (PRGNativeReductionConcrete.fixedCode O)
      (PRGNativeQueryBackend.witness G O true messages hWidth).resources n := by
  have hLeft := PRGNativeQueryBackend.witness_advantage G O false messages hWidth n
  have hRight := PRGNativeQueryBackend.witness_advantage G O true messages hWidth n
  rw [PRGNativeQueryBackend.witness_code] at hLeft hRight
  rw [hLeft, hRight]
  exact PRGNativePipeline.advantage_le I O n (messages n)

include hWidth in
/-- Computational security is invoked only for reductions whose concrete
class membership, stopping and resource bounds have already been proved. -/
theorem security_time_and_reduction_space
    (hSecure : (PRGNativeQueryBackend.registration G).object.Secure messages) :
    PolynomiallyBounded (PRGNativePipeline.timeBound I O) ∧
    PolynomiallyBounded (PRGNativeQueryExecution.timeBound G O) ∧
    PolynomiallyBounded (PRGNativeQueryExecution.bitBound G O) ∧
    Negligible (fun n => probabilityGap
      (eventProb (PRGNativePipeline.game I O n (messages n).1) (· = true))
      (eventProb (PRGNativePipeline.game I O n (messages n).2) (· = true))) := by
  refine ⟨PRGNativePipeline.time_polynomial I O hWidth,
    PRGNativeQueryExecution.time_polynomial G hWidth O,
    PRGNativeQueryExecution.space_polynomial G O hWidth, ?_⟩
  have hLeft := hSecure (PRGNativeQueryBackend.adversary G O false messages)
    (PRGNativeQueryBackend.witness G O false messages hWidth).admissible
  have hRight := hSecure (PRGNativeQueryBackend.adversary G O true messages)
    (PRGNativeQueryBackend.witness G O true messages hWidth).admissible
  exact Negligible.mono (fun n => PRGNativePipeline.advantage_le I O n (messages n)) (hLeft.add hRight)

end Foundation.Symmetric.PRGNativeQuerySecurity
