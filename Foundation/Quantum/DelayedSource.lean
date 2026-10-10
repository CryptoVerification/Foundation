import Foundation.Quantum.SourceReplacement
import Foundation.Quantum.LocalOperations

/-! Delaying the source-side basis operation until after the entire adversarial
channel. The input pair and the attack are independent of that later basis. -/
namespace Foundation.Quantum.SourceReplacement
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {a b : Space}

theorem rotate_commute (C : Channel a b) (U : Operator a) (hU : U.conjTranspose*U = 1)
    (ρ : Density (.tensor a a)) :
    ((C.amplify a).run ((rotate a a U hU).run ρ)).matrix =
      ((rotate a b U hU).run ((C.amplify a).run ρ)).matrix := by
  change (C.toKraus.amplify a).apply ((Kraus.single _).apply ρ.matrix) = (Kraus.single _).apply _
  simp only [Kraus.single_apply]
  exact Kraus.commute_right C.toKraus U ρ.matrix

def delayed (a : Space) (c : ℂ) (hc : (Fintype.card a.Basis:ℂ)*(c*star c) = 1)
    (U : Operator a) (hU : U.conjTranspose*U = 1) (C : Channel a b) : Density (.tensor b a) :=
  (rotate a b U hU).run ((C.amplify a).run (pair a c hc))

/-- Alice's actual delayed outcome block equals the uniformly weighted remote
prepare-and-send experiment, including every retained adversarial coordinate. -/
theorem delayed_replacement (a : Space) (c : ℂ) (hc : (Fintype.card a.Basis:ℂ)*(c*star c) = 1)
    (U : Operator a) (hU : U.conjTranspose*U = 1) (hsym : ∀ i j, U i j = U j i)
    (C : Channel a b) (x : a.Basis) :
    slice (delayed a c hc U hU C).matrix x =
      (c*star c) • (C.run ((Channel.ofIsometry U hU).run (basisDensity a x))).matrix := by
  unfold delayed
  rw [← rotate_commute]
  exact replacement a c hc U hU hsym C x

end
end Foundation.Quantum.SourceReplacement
