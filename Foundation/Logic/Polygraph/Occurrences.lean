import Foundation.Logic.Polygraph.Presentation
import Mathlib.Data.List.FinRange

/-! Ordered leaf occurrences, including repeated uses of the same assumption.
Substitution expands each occurrence, rather than taking a set of indices. -/
namespace Foundation.Logic.Derivation

universe j r
variable {T : Presentation.{j, r}} {Γ Δ : Context T}

def occurrences {A} : Derivation T Γ A → List (Fin Γ.length)
  | .hypothesis i => [i]
  | .apply rule children => (List.finRange (T.arity rule)).flatMap
      (fun i => occurrences (children i))

theorem occurrences_substitute {A} (d : Derivation T Γ A)
    (replacement : ∀ i, Derivation T Δ (Γ.claim i)) :
    (d.substitute replacement).occurrences =
      d.occurrences.flatMap (fun i => (replacement i).occurrences) := by
  induction d with
  | hypothesis i => simp [substitute, occurrences]
  | apply rule children ih => simp [substitute, occurrences, ih, List.flatMap_assoc]

end Foundation.Logic.Derivation

namespace Foundation.Logic.Polygraph.Diagram

universe j r

/-- Outputs are traversed in order; within each output, premises are traversed
in their registered order. Sharing a context does not merge leaf occurrences. -/
def occurrences {T : Presentation.{j, r}} {Γ Δ : Logic.Context T}
    (d : Diagram T Γ Δ) : List (Fin Γ.length) :=
  (List.finRange Δ.length).flatMap (fun i => (toForest d i).occurrences)

end Foundation.Logic.Polygraph.Diagram
