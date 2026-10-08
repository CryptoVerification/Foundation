import Foundation.Crypto.Logic.General.FreshMaskAdaptiveFirstArrivalBackend

/-! An inhabited goal-to-runtime registration, including actual first-halt
time and full-prefix storage. The goal measures a fixed arbitrary public
event, not an implemented adversary program. Its advantage is the actual
experiment gap, rather than a stipulated zero. -/
namespace Foundation.Examples.FreshMaskAdaptiveRegisteredSecurity
open Foundation.Probability TimedExecution Foundation.Symmetric
open CryptoOracle.Interactive CryptoLogic.General
set_option backward.isDefEq.respectTransparency false

variable (rounds width : Nat → Nat) (observer : CryptoOracle.Interactive.Control × Nat → Bool)

noncomputable def game (n : Nat) (messages : Bits (width n) × Bits (width n)) (side : Bool) : PMF Bool :=
  (FreshMaskAdaptiveExecution.law (rounds n) () []
    (if side then messages.2 else messages.1).toList []).map
      (fun frame => observer (frame.control, FreshMaskAdaptiveExecution.timeBound (rounds n) (width n)))

noncomputable def goal : CryptoGoal where
  Instance := fun n => Bits (width n) × Bits (width n)
  Adversary := fun _ _ => Unit
  advantage := fun n messages _ => probabilityGap
    (eventProb (game rounds width observer n messages false) (· = true))
    (eventProb (game rounds width observer n messages true) (· = true))

noncomputable def modelGame (F : InstanceFamily (goal rounds width observer))
    (_ : AdversaryFamily (goal rounds width observer) F) (n : Nat) (side : Bool) : PMF Bool :=
  game rounds width observer n (F n) side

theorem advantage_eq (F A n) : advantageProfile (goal rounds width observer) F A n =
    probabilityGap (eventProb (modelGame rounds width observer F A n false) (· = true))
      (eventProb (modelGame rounds width observer F A n true) (· = true)) := rfl

noncomputable def profile := FreshMaskAdaptiveFirstArrivalBackend.profile observer (goal rounds width observer) rounds width
  (fun _ => ()) (fun _ messages side => if side then messages.2 else messages.1)

theorem realizes (F : InstanceFamily (goal rounds width observer))
    (A : AdversaryFamily (goal rounds width observer) F) (n : Nat) (side : Bool) :
    (profile rounds width observer).logicalGame (FreshMaskAdaptiveFirstArrivalBackend.runtime Unit observer)
      AdaptiveBitstringLoop.code n (F n) side = modelGame rounds width observer F A n side := by
  simp only [profile, FirstArrivalObservedBackend.Profile.logicalGame, FreshMaskAdaptiveFirstArrivalBackend.profile,
    FreshMaskAdaptiveFirstArrivalBackend.runtime, PMF.map_comp, Function.comp_def, FreshMaskAdaptiveExecution.publicControl]
  rfl

variable (F : InstanceFamily (goal rounds width observer))
    (A : AdversaryFamily (goal rounds width observer) F)

noncomputable def witness (hRounds : PolynomiallyBounded rounds) (hWidth : PolynomiallyBounded width) :
    (FirstArrivalObservedBackend.registration (FreshMaskAdaptiveFirstArrivalBackend.runtime Unit observer)
      (modelGame rounds width observer) (advantage_eq rounds width observer)).object.Witness F A :=
  FreshMaskAdaptiveFirstArrivalBackend.witness (P := goal rounds width observer) observer rounds width (fun _ => ())
    (fun _ messages side => if side then messages.2 else messages.1) F
    (modelGame rounds width observer) (advantage_eq rounds width observer) A hRounds hWidth
    (realizes rounds width observer F A)

noncomputable def peakWitness (hRounds : PolynomiallyBounded rounds) (hWidth : PolynomiallyBounded width) :
    (FirstArrivalObservedBackend.peakRegistration (FreshMaskAdaptiveFirstArrivalBackend.runtime Unit observer)
      (modelGame rounds width observer) (advantage_eq rounds width observer)
      (FreshMaskAdaptiveFirstArrivalBackend.measure FreshMaskAdaptiveResources.unitEncoding)).object.Witness F A :=
  FreshMaskAdaptiveFirstArrivalBackend.peakWitness (P := goal rounds width observer) observer rounds width (fun _ => ())
    (fun _ messages side => if side then messages.2 else messages.1) F
    (modelGame rounds width observer) (advantage_eq rounds width observer) A
    FreshMaskAdaptiveResources.unitEncoding (fun _ => 0)
    (by intro state; cases state; rfl) (PolynomiallyBounded.const 0) hRounds hWidth
    (realizes rounds width observer F A)

theorem advantage_zero (hPositive : ∀ n, 0 < rounds n) (n : Nat) :
    advantageProfile (goal rounds width observer) F A n = 0 :=
  FreshMaskAdaptiveFirstArrivalBackend.advantage_zero (P := goal rounds width observer) observer rounds width (fun _ => ())
    (fun _ messages side => if side then messages.2 else messages.1) F
    (modelGame rounds width observer) (advantage_eq rounds width observer) A hPositive
    (realizes rounds width observer F A) n

theorem negligible_advantage (hPositive : ∀ n, 0 < rounds n) :
    Negligible (advantageProfile (goal rounds width observer) F A) := by
  have h : advantageProfile (goal rounds width observer) F A = fun _ => 0 :=
    funext (advantage_zero rounds width observer F A hPositive)
  rw [h]
  exact Negligible.zero

end Foundation.Examples.FreshMaskAdaptiveRegisteredSecurity
