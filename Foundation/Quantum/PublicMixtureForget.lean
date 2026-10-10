import Foundation.Quantum.PublicMixtureObservation
import Foundation.Quantum.InstrumentForgetRecord

/-! Physical removal of a redundant public seed gives the actual weighted
operator mixture, with all remaining public and quantum registers retained. -/
namespace Foundation.Quantum
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem publicMixture_forget {S : Type} [Fintype S] [DecidableEq S] {a : Space}
    (p : PMF S) (A : S → Operator a) :
    (Instrument.forgetRecord a (Fintype.card S)).toKraus.apply (publicMixture p A) =
      ∑ s, ((p s).toReal : ℂ) • A s := by
  rw [Instrument.forgetRecord_apply]
  ext i j
  simp only [Matrix.sum_apply, Finset.sum_apply, Matrix.smul_apply, smul_eq_mul]
  change (∑ r : Fin (Fintype.card S), publicMixture p A (r,i) (r,j)) =
    ∑ s : S, ((p s).toReal : ℂ) * A s i j
  calc
    _ = ∑ s : S, publicMixture p A (Fintype.equivFin S s,i) (Fintype.equivFin S s,j) :=
      (Equiv.sum_comp (Fintype.equivFin S) (fun r => publicMixture p A (r,i) (r,j))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [publicMixture_block]
      simp only [ite_true]

end
end Foundation.Quantum
