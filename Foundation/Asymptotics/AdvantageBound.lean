import Foundation.Asymptotics.Negligible
import Foundation.Core.Bound

open scoped ENNReal

namespace AdvantageBound

/-- An advantage loss maps every negligible function to a negligible
function. Monotonicity alone does not imply this property. -/
def PreservesNegligible (L : AdvantageBound) : Prop :=
  ∀ (ε : Nat → ℝ≥0∞), Negligible ε →
    Negligible (fun n => L.eval n (ε n))

theorem id_preservesNegligible : AdvantageBound.id.PreservesNegligible := by
  intro ε hε
  exact hε

/-- `f.comp g` applies `g` first, then `f`, so preservation follows in
that same order. -/
theorem comp_preservesNegligible (f g : AdvantageBound)
    (hf : f.PreservesNegligible) (hg : g.PreservesNegligible) :
    (f.comp g).PreservesNegligible := by
  intro ε hε
  exact hf (fun n => g.eval n (ε n)) (hg ε hε)

end AdvantageBound
