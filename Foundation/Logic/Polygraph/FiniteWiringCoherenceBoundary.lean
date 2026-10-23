import Foundation.Logic.Polygraph.FiniteWiringCoherence

/-! The eleven forms are schematic, not uniformly bounded elementary
four-diagrams. Even with one input/output, a single root-square instance can
have an arbitrarily long normalized boundary. This does NOT rule out some
other bounded or critical-overlap presentation. -/
namespace Foundation.Logic.Polygraph.FiniteWiring.Higher.Boundary

def tower : Nat → Circuit 1 1
  | 0 => .identity 1
  | depth + 1 => .seq (tower depth) (.identity 1)

theorem tower_steps (depth : Nat) : (normalize (tower depth)).steps = 4 * depth + 2 := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    change (normalize (tower depth)).steps + 2 + 2 = 4 * (depth + 1) + 2
    rw [ih]
    omega

def boundaryLeft (depth : Nat) : Cell (.seq (tower depth) (.identity 1)) (normal (tower depth).routing) :=
  .trans (.seqRightUnit (tower depth)) (normalize (tower depth))

/-- One root-square schema, instantiated with a larger term parameter. -/
def rootSquare (depth : Nat) : Generator (boundaryLeft depth) (normalize (.seq (tower depth) (.identity 1))) :=
  .root (.seqRightUnit (tower depth)) (tower depth).routing rfl

theorem boundary_steps (depth : Nat) : (boundaryLeft depth).steps = 4 * depth + 3 := by
  change 1 + (normalize (tower depth)).steps = _
  rw [tower_steps]
  omega

theorem boundaries_unbounded (limit : Nat) : ∃ depth, limit < (boundaryLeft depth).steps := by
  refine ⟨limit, ?_⟩
  rw [boundary_steps]
  omega

end Foundation.Logic.Polygraph.FiniteWiring.Higher.Boundary
