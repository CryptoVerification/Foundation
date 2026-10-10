import Foundation.Quantum.QKD.KeyVerificationPrivacy
import Foundation.Quantum.QKD.SubnormalizedMixture

namespace Foundation.Quantum.QKD.KeyVerification
noncomputable section
open Subnormalized
set_option backward.isDefEq.respectTransparency false
variable {K T S V : Type} [Fintype K] [Fintype T] [Fintype S] [Fintype V]
  [DecidableEq K] [DecidableEq T] [DecidableEq S] [DecidableEq V] {e : Space}

/-- Exact agreement with the previously implemented independently seeded
check, including all old public data, the tag and the original quantum blocks. -/
theorem accepted_mixture (ρ : State (Input K T) e) (p : PMF S) (hash : S → K → V) :
    accepted ρ p hash = mixture p (fun s =>
      relabel (selected ρ hash s) (fun x => acceptLabel hash (s,x))) := by
  apply State.ext
  funext y
  simp only [accepted, mixture, relabel, seed, restrict, selected, Fintype.sum_prod_type,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro t _
  by_cases he : acceptLabel hash (s,((a,b),t)) = y <;>
    by_cases hp : hash s a = hash s b <;>
    simp only [passes, he, hp, ite_true, ite_false, smul_zero]

end
end Foundation.Quantum.QKD.KeyVerification
