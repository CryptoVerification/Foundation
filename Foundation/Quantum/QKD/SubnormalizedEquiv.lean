import Foundation.Quantum.QKD.SubnormalizedRelabel

namespace Foundation.Quantum.QKD.Subnormalized
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem relabel_equiv_block {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    {e : Space} (ρ : State X e) (f : X ≃ Y) (y : Y) :
    (relabel ρ f).block y = ρ.block (f.symm y) := by
  classical
  have hf (x : X) : f x = y ↔ x = f.symm y := f.eq_symm_apply.symm
  simp [relabel, hf]

end
end Foundation.Quantum.QKD.Subnormalized
