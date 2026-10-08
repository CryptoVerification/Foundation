import Foundation.Crypto.Logic.General.ObservedExecution

/-! Add independently checkable resource certificates to an existing observed
execution backend. Finite code, runtime contexts, horizons, games and previous
certificates are preserved. The new certificate must be proved, not asserted. -/
namespace CryptoLogic.General.ObservedExecution
open Foundation.Probability
universe u v w
variable {K : CodeSystem} {m : K.Machine} {P : CryptoGoal.{u}}
    (B : ObservedExecution.{u,v} K m P) (Extra : Type w)
    (certified : InstanceFamily P → K.Code m → B.Resources → Extra → Prop)

noncomputable def certify : ObservedExecution K m P where
  Resources := B.Resources × Extra
  ExecutesWithin := fun F code resources =>
    B.ExecutesWithin F code resources.1 ∧ certified F code resources.1 resources.2
  game := fun F code resources => B.game F code resources.1
  modelGame := B.modelGame
  advantage_eq := B.advantage_eq

noncomputable def certifyWitness (F A) (W : B.object.Witness F A) (extra : Extra)
    (h : certified F W.code W.resources extra) : (certify B Extra certified).object.Witness F A :=
  ⟨W.code, (W.resources, extra), ⟨W.executes, h⟩, W.realizes,
    ⟨W.code, (W.resources, extra), ⟨W.executes, h⟩, W.realizes⟩⟩

def forgetCertificate (F A) (W : (certify B Extra certified).object.Witness F A) : B.object.Witness F A :=
  ⟨W.code, W.resources.1, W.executes.1, W.realizes,
    ⟨W.code, W.resources.1, W.executes.1, W.realizes⟩⟩

theorem certifyWitness_code (F A) (W : B.object.Witness F A) (extra : Extra)
    (h : certified F W.code W.resources extra) :
    (certifyWitness B Extra certified F A W extra h).code = W.code := rfl

theorem certifyWitness_resources (F A) (W : B.object.Witness F A) (extra : Extra)
    (h : certified F W.code W.resources extra) :
    (certifyWitness B Extra certified F A W extra h).resources.1 = W.resources := rfl

theorem forgetCertificate_code (F A) (W : (certify B Extra certified).object.Witness F A) :
    (forgetCertificate B Extra certified F A W).code = W.code := rfl

theorem nativeAdvantage_certify (F : InstanceFamily P) (code : K.Code m)
    (resources : B.Resources) (extra : Extra) (n : Nat) :
    (certify B Extra certified).nativeAdvantage F code (resources, extra) n =
      B.nativeAdvantage F code resources n := rfl

/-- Security for the original larger class implies security for its
certificate-bearing subclass. The reverse implication is not assumed. -/
theorem secure_certify (F : InstanceFamily P) (hSecure : B.object.Secure F) :
    (certify B Extra certified).object.Secure F := by
  intro A hA
  obtain ⟨code, resources, hExec, hReal⟩ := hA
  exact hSecure A ⟨code, resources.1, hExec.1, hReal⟩

end CryptoLogic.General.ObservedExecution
