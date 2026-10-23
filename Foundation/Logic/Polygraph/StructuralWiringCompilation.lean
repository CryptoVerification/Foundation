import Foundation.Logic.Polygraph.FiniteWiring
import Foundation.Logic.Polygraph.StructuralTransport

/-! Compositional compilation of one-sort structural product shapes to the
complete finite-product wiring calculus. Source seq/tensor nodes are retained.
Copy/discard/symmetry/unit gates expand only into their immediate wiring.
This is not a proof of higher coherence of the source nine-rule Cell language. -/
namespace Foundation.Logic.Polygraph.StructuralTransport.Finite
open Foundation.Logic.Polygraph.FiniteWiring (Circuit)

abbrev Values (A : Type) (shape : Shape Unit) := shape.Value (fun _ => A)

abbrev arity : Shape Unit → Nat
  | .atom _ => 1
  | .unit => 0
  | .pair first second => arity first + arity second

def flatten {A : Type} : (shape : Shape Unit) → Values A shape → Fin (arity shape) → A
  | .atom _, value, _ => value
  | .unit, _, index => Fin.elim0 index
  | .pair first second, value, index => Fin.addCases (flatten first value.1) (flatten second value.2) index

def unflatten {A : Type} : (shape : Shape Unit) → (Fin (arity shape) → A) → Values A shape
  | .atom _, environment => environment 0
  | .unit, _ => PUnit.unit
  | .pair first second, environment =>
      (unflatten first (fun i => environment (Fin.castAdd (arity second) i)),
       unflatten second (fun i => environment (Fin.natAdd (arity first) i)))

theorem unflatten_flatten {A : Type} (shape : Shape Unit) (value : Values A shape) :
    unflatten shape (flatten shape value) = value := by
  induction shape with
  | atom => rfl
  | unit => cases value; rfl
  | pair first second one two =>
    apply Prod.ext
    · simpa only [unflatten, flatten, Fin.addCases_left] using one value.1
    · simpa only [unflatten, flatten, Fin.addCases_right] using two value.2

theorem flatten_unflatten {A : Type} (shape : Shape Unit) (environment : Fin (arity shape) → A) :
    flatten shape (unflatten shape environment) = environment := by
  funext index
  induction shape with
  | atom =>
    have same : index = 0 := Subsingleton.elim _ _
    subst index
    rfl
  | unit => exact Fin.elim0 index
  | pair first second one two =>
    refine Fin.addCases ?_ ?_ index
    · intro i; simpa only [unflatten, flatten, Fin.addCases_left] using one (fun j => environment (Fin.castAdd (arity second) j)) i
    · intro i; simpa only [unflatten, flatten, Fin.addCases_right] using two (fun j => environment (Fin.natAdd (arity first) j)) i

def compile : {first last : Shape Unit} → Wire first last → Circuit (arity first) (arity last)
  | _, _, .identity _ => .identity _
  | _, _, .seq first second => .seq (compile first) (compile second)
  | _, _, .tensor first second => .tensor (compile first) (compile second)
  | _, _, .copy _ => .tuple (Fin.addCases (fun index => .select index) (fun index => .select index))
  | _, _, .discard _ => .tuple Fin.elim0
  | _, _, .swap first second => .tuple (Fin.addCases
      (fun index => .select (Fin.natAdd (arity first) index))
      (fun index => .select (Fin.castAdd (arity second) index)))
  | _, _, .assoc first second third => .tuple (Fin.addCases
      (fun index => .select (Fin.castAdd (arity third) (Fin.castAdd (arity second) index)))
      (Fin.addCases
        (fun index => .select (Fin.castAdd (arity third) (Fin.natAdd (arity first) index)))
        (fun index => .select (Fin.natAdd (arity first + arity second) index))))
  | _, _, .unassoc first second third => .tuple (Fin.addCases
      (Fin.addCases
        (fun index => .select (Fin.castAdd (arity second + arity third) index))
        (fun index => .select (Fin.natAdd (arity first) (Fin.castAdd (arity third) index))))
      (fun index => .select (Fin.natAdd (arity first) (Fin.natAdd (arity second) index))))
  | _, _, .leftUnit _ => .tuple (fun index => .select (Fin.natAdd 0 index))
  | _, _, .leftUnitInv _ => .tuple (Fin.addCases Fin.elim0 (fun index => .select index))
  | _, _, .rightUnit _ => .tuple (fun index => .select (Fin.castAdd 0 index))
  | _, _, .rightUnitInv _ => .tuple (Fin.addCases (fun index => .select index) Fin.elim0)

theorem compile_correct {A : Type} {first last : Shape Unit} (wire : Wire first last)
    (value : Values A first) (index : Fin (arity last)) :
    (compile wire).eval (flatten first value) index = flatten last (wire.eval (fun _ => A) value) index := by
  induction wire with
  | identity => rfl
  | seq first second one two =>
    change (compile second).eval ((compile first).eval (flatten _ value)) index = _
    rw [show (compile first).eval (flatten _ value) = flatten _ (first.eval (fun _ => A) value) from funext (one value)]
    exact two (first.eval (fun _ => A) value) index
  | tensor first second one two =>
    refine Fin.addCases ?_ ?_ index
    · intro i; simpa only [compile, Circuit.eval, flatten, Wire.eval, Fin.addCases_left] using one value.1 i
    · intro i; simpa only [compile, Circuit.eval, flatten, Wire.eval, Fin.addCases_right] using two value.2 i
  | copy =>
    refine Fin.addCases ?_ ?_ index
    · intro i; simp only [compile, Circuit.eval, flatten, Wire.eval, Fin.addCases_left]
    · intro i; simp only [compile, Circuit.eval, flatten, Wire.eval, Fin.addCases_right]
  | discard => exact Fin.elim0 index
  | swap =>
    refine Fin.addCases ?_ ?_ index
    · intro i; simp only [compile, Circuit.eval, flatten, Wire.eval, Fin.addCases_left, Fin.addCases_right]
    · intro i; simp only [compile, Circuit.eval, flatten, Wire.eval, Fin.addCases_right, Fin.addCases_left]
  | assoc =>
    refine Fin.addCases ?_ ?_ index
    · intro i; simp only [compile, Circuit.eval, flatten, Wire.eval, Fin.addCases_left]
    · intro rest
      refine Fin.addCases ?_ ?_ rest
      · intro i; simp only [compile, Circuit.eval, flatten, Wire.eval, Fin.addCases_left, Fin.addCases_right]
      · intro i; simp only [compile, Circuit.eval, flatten, Wire.eval, Fin.addCases_right]
  | unassoc =>
    refine Fin.addCases ?_ ?_ index
    · intro rest
      refine Fin.addCases ?_ ?_ rest
      · intro i; simp only [compile, Circuit.eval, flatten, Wire.eval, Fin.addCases_left]
      · intro i; simp only [compile, Circuit.eval, flatten, Wire.eval, Fin.addCases_left, Fin.addCases_right]
    · intro i; simp only [compile, Circuit.eval, flatten, Wire.eval, Fin.addCases_right]
  | leftUnit => simp only [compile, Circuit.eval, flatten, Wire.eval, Fin.addCases_right]
  | leftUnitInv =>
    refine Fin.addCases ?_ ?_ index
    · intro i; exact Fin.elim0 i
    · intro i; simp only [compile, Circuit.eval, flatten, Wire.eval, Fin.addCases_right]
  | rightUnit => simp only [compile, Circuit.eval, flatten, Wire.eval, Fin.addCases_left]
  | rightUnitInv =>
    refine Fin.addCases ?_ ?_ index
    · intro i; simp only [compile, Circuit.eval, flatten, Wire.eval, Fin.addCases_left]
    · intro i; exact Fin.elim0 i

theorem compiled_cell_sound {A : Type} {first last : Shape Unit} {one two : Wire first last}
    (cell : FiniteWiring.Cell (compile one) (compile two)) (value : Values A first) :
    one.eval (fun _ => A) value = two.eval (fun _ => A) value := by
  have arrays : flatten last (one.eval (fun _ => A) value) = flatten last (two.eval (fun _ => A) value) := by
    funext index
    rw [← compile_correct, ← compile_correct]
    exact congrFun (cell.sound (flatten first value)) index
  have values := congrArg (unflatten last) arrays
  simpa only [unflatten_flatten] using values

theorem complete {first last : Shape Unit} (one two : Wire first last) :
    Nonempty (FiniteWiring.Cell (compile one) (compile two)) ↔
      ∀ (A : Type) (value : Values A first), one.eval (fun _ => A) value = two.eval (fun _ => A) value := by
  constructor
  · rintro ⟨cell⟩ A value
    exact compiled_cell_sound cell value
  · intro equal
    apply (FiniteWiring.all_models_iff (compile one) (compile two)).mp
    intro A environment
    funext index
    have same := congrArg (fun value => flatten last value index) (equal A (unflatten first environment))
    rw [← compile_correct, ← compile_correct, flatten_unflatten] at same
    exact same

/-- Completeness also holds for arbitrary correlated input laws, across all
interpretations of the one atomic type. This is not completeness for a fixed
singleton-reference model or for arbitrary stochastic operation boxes. -/
theorem probabilistic_complete {first last : Shape Unit} (one two : Wire first last) :
    Nonempty (FiniteWiring.Cell (compile one) (compile two)) ↔
      ∀ (A : Type) (law : PMF (Values A first)),
        law.map (one.eval (fun _ => A)) = law.map (two.eval (fun _ => A)) := by
  constructor
  · rintro ⟨cell⟩ A law
    exact congrArg (fun function => law.map function) (funext (compiled_cell_sound cell))
  · intro equal
    apply (complete one two).mpr
    intro A value
    have pureEqual := equal A (PMF.pure value)
    simp only [PMF.pure_map] at pureEqual
    have supported : one.eval (fun _ => A) value ∈ (PMF.pure (two.eval (fun _ => A) value)).support := by
      rw [← pureEqual]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
    exact (PMF.mem_support_pure_iff _ _).mp supported

end Foundation.Logic.Polygraph.StructuralTransport.Finite
