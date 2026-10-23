import Foundation.Crypto.Logic.Polygraph.GameProofOrdinaryErasure
import Foundation.Logic.SharedInferenceDerivation
import Foundation.Examples.GameProofMACNormalization

/-! An independently constructed ordinary finite-support proof for the MAC
chain. Its derivation builder uses the existing local comparison,
congruence, symmetry and transitivity without calling terminalCoherence or
constructing a Cell. The separate general-geometry comparison entry point
deliberately calls the old generated function. The specialization to this chain is an explicit comparison limitation.
The same derivation also admits the geometric model of the local rules. -/
namespace CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.OrdinaryMAC
open Foundation.Logic
open Foundation.Logic.SharedInference
open Foundation.Logic.Polygraph.ScheduleCertificate
set_option backward.isDefEq.respectTransparency false

def normal : (stage : Nat) → Plan MACNormalization.layout (.stage stage) .finish
  | 0 => .seq (MACNormalization.direct 0) (.identity MACNormalization.Vertex.finish)
  | stage + 1 => .seq (.atom (MACNormalization.Atom.schedule stage)) (normal stage)

theorem normal_eq (stage : Nat) : normal stage = MACNormalization.strategy.normal (.stage stage) := by
  induction stage with
  | zero =>
    have step := MACNormalization.strategy.normal_step (MACNormalization.Atom.eliminate 0) rfl
    change MACNormalization.strategy.normal (.stage 0) =
      .seq (MACNormalization.direct 0) (MACNormalization.strategy.normal MACNormalization.Vertex.finish) at step
    rw [MACNormalization.strategy.normal_sink] at step
    exact step.symm
  | succ stage ih =>
    change Plan.seq (.atom (MACNormalization.Atom.schedule stage)) (normal stage) = _
    rw [ih]
    exact (MACNormalization.strategy.normal_step (MACNormalization.Atom.schedule stage) rfl).symm

def rootSupport (stage : Nat) : Finset Nat :=
  (MACNormalization.relators stage).left.needs MACNormalization.layout ∪
    (MACNormalization.relators stage).right.needs MACNormalization.layout ∪ (MACNormalization.relators stage).needs

def support : Nat → Finset Nat
  | 0 => (MACNormalization.direct 0).needs MACNormalization.layout
  | stage + 1 => rootSupport stage ∪ (∅ ∪ support stage)

theorem support_range (stage : Nat) : support stage = Finset.range (stage + 1) := by
  induction stage with
  | zero => simp [support, MACNormalization.direct, Plan.needs, MACNormalization.layout]
  | succ stage ih =>
    change rootSupport stage ∪ (∅ ∪ support stage) = _
    rw [ih]
    ext label
    simp [rootSupport, MACNormalization.relators, Plan.needs, MACNormalization.layout]
    omega

def claim (stage : Nat) : CellPresentation.Claim MACNormalization.layout :=
  ⟨.stage stage, .finish, MACNormalization.direct stage, normal stage, support stage⟩

abbrev theory := CellPresentation.theory MACNormalization.layout MACNormalization.relators

def derivation : (stage : Nat) → Foundation.Logic.Derivation theory (Foundation.Logic.Context.empty theory) (claim stage)
  | 0 => Foundation.Logic.Derivation.apply (T := theory) (Γ := Foundation.Logic.Context.empty theory) (.symm (.seq (MACNormalization.direct 0) (.identity MACNormalization.Vertex.finish)) (MACNormalization.direct 0) (support 0))
      (fun _ => Foundation.Logic.Derivation.apply (T := theory) (Γ := Foundation.Logic.Context.empty theory) (.rightUnit (MACNormalization.direct 0)) (fun index => Fin.elim0 index))
  | stage + 1 =>
      let head : Plan MACNormalization.layout (.stage (stage + 1)) (.stage stage) := .atom (MACNormalization.Atom.schedule stage)
      let middle := Plan.seq head (MACNormalization.direct stage)
      let root : Foundation.Logic.Derivation theory (Foundation.Logic.Context.empty theory)
          ⟨_, _, middle, MACNormalization.direct (stage + 1), rootSupport stage⟩ := Foundation.Logic.Derivation.apply (T := theory) (Γ := Foundation.Logic.Context.empty theory) (.root stage) (fun index => Fin.elim0 index)
      let flipped : Foundation.Logic.Derivation theory (Foundation.Logic.Context.empty theory)
          ⟨_, _, MACNormalization.direct (stage + 1), middle, rootSupport stage⟩ :=
        Foundation.Logic.Derivation.apply (T := theory) (Γ := Foundation.Logic.Context.empty theory) (.symm middle (MACNormalization.direct (stage + 1)) (rootSupport stage)) (fun _ => root)
      let lifted : Foundation.Logic.Derivation theory (Foundation.Logic.Context.empty theory)
          ⟨_, _, middle, .seq head (normal stage), ∅ ∪ support stage⟩ :=
        Foundation.Logic.Derivation.apply (T := theory) (Γ := Foundation.Logic.Context.empty theory) (.seq head head (MACNormalization.direct stage) (normal stage) ∅ (support stage))
          (Fin.cases (Foundation.Logic.Derivation.apply (T := theory) (Γ := Foundation.Logic.Context.empty theory) (.refl head) (fun index => Fin.elim0 index)) (fun _ => derivation stage))
      Foundation.Logic.Derivation.apply (T := theory) (Γ := Foundation.Logic.Context.empty theory) (.trans (MACNormalization.direct (stage + 1)) middle (.seq head (normal stage))
        (rootSupport stage) (∅ ∪ support stage)) (Fin.cases flipped (fun _ => lifted))

def tree (stage : Nat) := closedTree (derivation stage)

theorem proof (orders : Nat → Schedule 8) (stage : Nat) :
    CellPresentation.FiniteOrdinary.Meaning (MACNormalization.model orders) (claim stage) :=
  (derivation stage).eval (CellPresentation.FiniteOrdinary.interpretation (MACNormalization.model orders)) (fun index => Fin.elim0 index)

def specializedGeometric (stage : Nat) :
    {cell : Cell MACNormalization.layout MACNormalization.relators (MACNormalization.direct stage) (normal stage) //
      cell.needs MACNormalization.layout MACNormalization.relators = support stage} :=
  (derivation stage).eval (CellPresentation.geometric MACNormalization.layout MACNormalization.relators) (fun i => Fin.elim0 i)

theorem exact_tree_agreement (stage : Nat) : CellPresentation.toTree (specializedGeometric stage).1 = tree stage :=
  CellPresentation.ordinary_geometric_tree MACNormalization.layout MACNormalization.relators (derivation stage)

theorem exact_compilation_agreement (stage : Nat) :
    SharedInference.compile (T := theory) (CellPresentation.toTree (specializedGeometric stage).1) =
      SharedInference.compile (T := theory) (tree stage) :=
  congrArg (SharedInference.compile (T := theory)) (exact_tree_agreement stage)

def compile (stage : Nat) := CellPresentation.FiniteOrdinary.compileAt (relators := MACNormalization.relators) (claim stage) (tree stage)

def compileSpecializedGeometric (stage : Nat) :=
  CellPresentation.FiniteOrdinary.compileAt (relators := MACNormalization.relators) (claim stage)
    (CellPresentation.toTree (specializedGeometric stage).1)

def compileGeneralGeometric (stage : Nat) :=
  CellPresentation.FiniteOrdinary.compileAt (relators := MACNormalization.relators) (claim stage)
    (CellPresentation.toTree (MACNormalization.generated stage))

theorem checked_compilation_agreement (stage : Nat) : compileSpecializedGeometric stage = compile stage :=
  congrArg (CellPresentation.FiniteOrdinary.compileAt (relators := MACNormalization.relators) (claim stage))
    (exact_tree_agreement stage)

theorem repaired (old updated : Nat → Schedule 8) (stage : Nat) (changed : Finset Nat)
    (cached : Holds (MACNormalization.condition old) (support stage))
    (unchanged : ∀ label ∉ changed, old label = updated label)
    (rechecked : Holds (MACNormalization.condition updated) (fresh (support stage) changed)) :
    ∃ left : Holds (MACNormalization.condition updated) ((MACNormalization.direct stage).needs MACNormalization.layout),
    ∃ right : Holds (MACNormalization.condition updated) ((normal stage).needs MACNormalization.layout),
    Comparison (evaluate (MACNormalization.baseModel updated) (MACNormalization.direct stage) left)
      (evaluate (MACNormalization.baseModel updated) (normal stage) right) := by
  apply CellPresentation.FiniteOrdinary.repaired (proof updated stage) changed cached _ rechecked
  intro label outside existing
  simpa only [MACNormalization.condition, ← unchanged label outside] using existing

theorem tree_count (stage : Nat) : (tree stage).nodeCount = 5 * stage + 2 := by
  induction stage with
  | zero => norm_num [tree, derivation, closedTree, Tree.nodeCount, List.ofFn_succ]
  | succ stage ih =>
    change (closedTree (derivation (stage + 1))).nodeCount = _
    simp [derivation, closedTree, Tree.nodeCount, List.ofFn_succ, tree] at ih ⊢
    omega

/-- info: [(0, 2, 1), (1, 7, 2), (2, 12, 3), (3, 17, 4), (4, 22, 5)] -/
#guard_msgs in
#eval [0, 1, 2, 3, 4].map (fun stage => (stage, (tree stage).nodeCount, (support stage).card))

/-- info: [(0, some (2, 1, 859), true), (1, some (7, 6, 4157), true), (2, some (12, 11, 8021), true), (3, some (17, 16, 12464), true), (4, some (22, 21, 17495), true)] -/
#guard_msgs (whitespace := lax) in
#eval [0, 1, 2, 3, 4].map (fun stage => (stage, (compile stage).map (fun output =>
  (output.data.nodeCount, output.data.referenceCount, (output.data.encode CellPresentation.render).utf8ByteSize)),
  (compileGeneralGeometric stage).isSome))

end CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements.Examples.OrdinaryMAC
