import Foundation.Crypto.Logic.General.ObservedExecution

/-! Restrict operational witnesses by a concrete environment predicate.
Runtime profiles may carry arbitrary contexts; applications can require the
exact intended challenge law/public inputs before registering class membership.
The realized game and finite code are preserved; no runtime cost is added. -/
namespace CryptoLogic.General.ObservedExecution
open Foundation.Probability
universe u v
variable {K : CodeSystem} {m : K.Machine} {P : CryptoGoal.{u}}
    (B : ObservedExecution.{u,v} K m P)
    (allowed : InstanceFamily P → K.Code m → B.Resources → Prop)

noncomputable def restrict : ObservedExecution K m P where
  Resources := B.Resources
  ExecutesWithin := fun F code resources => B.ExecutesWithin F code resources ∧ allowed F code resources
  game := B.game
  modelGame := B.modelGame
  advantage_eq := B.advantage_eq

noncomputable def restrictWitness (F A) (W : B.object.Witness F A)
    (hAllowed : allowed F W.code W.resources) : (restrict B allowed).object.Witness F A :=
  ⟨W.code, W.resources, ⟨W.executes, hAllowed⟩, W.realizes,
    ⟨W.code, W.resources, ⟨W.executes, hAllowed⟩, W.realizes⟩⟩

def forgetRestriction (F A) (W : (restrict B allowed).object.Witness F A) : B.object.Witness F A :=
  ⟨W.code, W.resources, W.executes.1, W.realizes,
    ⟨W.code, W.resources, W.executes.1, W.realizes⟩⟩

theorem restrictWitness_code (F A) (W : B.object.Witness F A)
    (hAllowed : allowed F W.code W.resources) : (restrictWitness B allowed F A W hAllowed).code = W.code := rfl

theorem forgetRestriction_code (F A) (W : (restrict B allowed).object.Witness F A) :
    (forgetRestriction B allowed F A W).code = W.code := rfl

end CryptoLogic.General.ObservedExecution
