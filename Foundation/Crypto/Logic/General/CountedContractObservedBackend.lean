import Foundation.Crypto.Logic.General.ContractObservedBackend
import Foundation.Crypto.Semantics.OneUseCounter

/-! Register query/event bounds alongside completed operational contracts.
The counter is proof instrumentation: it preserves the original execution
marginal and adds no runtime transition. Applicable to arbitrary runtimes. -/
namespace CryptoLogic.General.ContractObservedBackend.Counted
open Foundation.Probability TimedExecution
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {K : CodeSystem} {m : K.Machine} {P : CryptoGoal.{u}}
    (R : Runtime.{v,w} K m)
    (event : K.Code m → R.Context → R.State → Bool)

def WithinEvents (r : Profile P R) (cap : Nat → Nat) (F : InstanceFamily P) (code : K.Code m) : Prop :=
  PolynomiallyBounded cap ∧ ∀ n side elapsed, elapsed ≤ r.horizon n →
    ∀ target ∈ (TimedExecution.eval
      (OneUseCounter.countedStep (R.step code (r.context n (F n) side))
        (event code (r.context n (F n) side))) elapsed
      (R.initial code (r.context n (F n) side), 0)).support, target.2 ≤ cap n

variable (modelGame : ∀ F : InstanceFamily P, AdversaryFamily P F → Nat → Bool → PMF Bool)
    (hAdvantage : ∀ F A n, advantageProfile P F A n =
      probabilityGap (eventProb (modelGame F A n false) (· = true))
        (eventProb (modelGame F A n true) (· = true)))

noncomputable def registration : ObservedExecution K m P where
  Resources := Profile P R × (Nat → Nat)
  ExecutesWithin := fun F code r => r.1.ExecutesWithin R F code ∧ WithinEvents R event r.1 r.2 F code
  game := fun F code r => r.1.nativeGame R F code
  modelGame := modelGame
  advantage_eq := hAdvantage

def witness (F A) (code : K.Code m) (r : Profile P R) (cap : Nat → Nat)
    (hExec : r.ExecutesWithin R F code) (hCount : WithinEvents R event r cap F code)
    (hLogical : ∀ n side, r.logicalGame code n (F n) side = modelGame F A n side) :
    (registration R event modelGame hAdvantage).object.Witness F A := by
  have hReal : (registration R event modelGame hAdvantage).Realizes F A code (r, cap) := by
    intro n side
    exact (r.nativeGame_eq R F code hExec n side).trans (hLogical n side)
  exact ⟨code, (r, cap), ⟨hExec, hCount⟩, hReal, ⟨code, (r, cap), ⟨hExec, hCount⟩, hReal⟩⟩

/-- Forgetting event evidence changes neither finite code, runtime profile,
nor realized game. It only enlarges the represented adversary class. -/
def forgetCounts (F A) (W : (registration R event modelGame hAdvantage).object.Witness F A) :
    (ContractObservedBackend.registration R modelGame hAdvantage).object.Witness F A :=
  ⟨W.code, W.resources.1, W.executes.1, W.realizes,
    ⟨W.code, W.resources.1, W.executes.1, W.realizes⟩⟩

theorem forgetCounts_code (F A) (W : (registration R event modelGame hAdvantage).object.Witness F A) :
    (forgetCounts R event modelGame hAdvantage F A W).code = W.code := rfl

end CryptoLogic.General.ContractObservedBackend.Counted
