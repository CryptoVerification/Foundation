import Foundation.Quantum.Contexts
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace Foundation.Quantum.ContextExamples
open Foundation.Logic
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Algebra := ℂ × ℂ

def scalarContext : Bohr.Context Algebra where
  algebra := ⊥
  closed := (⊥ : StarSubalgebra ℂ Algebra).toSubalgebra.toSubmodule.closed_of_finiteDimensional
  commutative x y := mul_comm x y

def fullContext : Bohr.Context Algebra where
  algebra := ⊤
  closed := isClosed_univ
  commutative x y := mul_comm x y

def observation : Algebra := (0, 1)
def available : Bohr.Persistent Algebra := Bohr.Persistent.contains observation

theorem not_available_in_scalars : ¬available.holds scalarContext := by
  intro h
  change observation ∈ (⊥ : StarSubalgebra ℂ Algebra) at h
  obtain ⟨z, hz⟩ := StarSubalgebra.mem_bot.mp h
  have h0 := congrArg Prod.fst hz
  have h1 := congrArg Prod.snd hz
  change z = 0 at h0
  change z = 1 at h1
  exact zero_ne_one (h0.symm.trans h1)

/-- Future-context implication is genuinely intuitionistic in a concrete model. -/
theorem excluded_middle_not_forced :
    ¬(Bohr.Persistent.join available
      (Bohr.Persistent.imp available Bohr.Persistent.bottom)).holds scalarContext := by
  intro h
  rcases h with h | h
  · exact not_available_in_scalars h
  · exact h fullContext (by change (⊥ : StarSubalgebra ℂ Algebra) ≤ ⊤; exact le_top) (by trivial)

/-- A false semantic entailment has no closed proof in the reconstructed calculus. -/
theorem excluded_middle_not_derivable : IsEmpty
    (Derivation Bohr.presentation (Context.empty Bohr.presentation)
      (.top, .join (.atom 0) (.imp (.atom 0) .bottom))) where
  false d := by
    have h := Bohr.sound Algebra (fun _ => available) d (fun i => Fin.elim0 i)
    exact excluded_middle_not_forced (h scalarContext trivial)

end
end Foundation.Quantum.ContextExamples
