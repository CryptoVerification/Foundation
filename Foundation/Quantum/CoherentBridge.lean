import Foundation.Quantum.Semantics
import Foundation.Quantum.Channels

/-! Sound transport from the original operation-equation logic to density
operators. Equal coherent matrices induce equal positive maps, also with an
auxiliary system. Trace preservation still requires an isometry proof. -/
namespace Foundation.Quantum
open Foundation.Logic
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem coherent_action_sound (σ : Assignment) {Γ : Context presentation} {j : Equation}
    (d : Derivation presentation Γ j) (h : ∀ i, (Γ.claim i).Valid σ)
    (ρ : Operator j.source) :
    (Kraus.single (j.lhs.eval σ)).apply ρ = (Kraus.single (j.rhs.eval σ)).apply ρ :=
  congrArg (fun M => (Kraus.single M).apply ρ) (sound σ d h)

theorem coherent_auxiliary_sound (σ : Assignment) {Γ : Context presentation} {j : Equation}
    (d : Derivation presentation Γ j) (h : ∀ i, (Γ.claim i).Valid σ)
    (e : Space) (ρ : Operator (.tensor j.source e)) :
    ((Kraus.single (j.lhs.eval σ)).amplify e).apply ρ =
      ((Kraus.single (j.rhs.eval σ)).amplify e).apply ρ :=
  congrArg (fun M => ((Kraus.single M).amplify e).apply ρ) (sound σ d h)

theorem approximate_of_coherent_eq {a b} (M N : Op a b)
    (hM : M.conjTranspose * M = 1) (hN : N.conjTranspose * N = 1) (h : M = N) :
    Approx (Channel.ofIsometry M hM) (Channel.ofIsometry N hN) 0 := by
  subst N
  exact Approx.refl _

end
end Foundation.Quantum
