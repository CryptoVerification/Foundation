import Foundation.Crypto.Meta.MultiExtraction
import Foundation.Crypto.Semantics.Security.ThreeGames
import Foundation.Examples.MachinePPT

namespace CryptoLogic.MultiExamples

open Machine Machine.Examples Foundation.Probability
open scoped ENNReal

inductive Object where
  | endpoint | left | right
  deriving DecidableEq, Repr

inductive Primitive : Object → Object → Type where
  | append (X) : Primitive X X

inductive Binary : Object → Object → Object → Type where
  | hybrid : Binary .endpoint .left .right

def language : MultiLanguage where
  unary := {
    Object := Object
    Primitive := Primitive
    primitiveCompiler := fun _ => .suffix [.halt] }
  Binary := Binary
  compilers := fun _ => (.identity, .identity)

set_option backward.isDefEq.respectTransparency false in
noncomputable def appendCertificate (g h : ThreeGames.Game) :
    CertifiedReduction (ThreeGames.object g h) (ThreeGames.object g h) :=
  { CertifiedReduction.id (ThreeGames.object g h) with
    compiler := .suffix [.halt]
    halts := fun p input => (haltsWithin_append_halt_iff _ _ _).2 (p.halts input)
    realizes := by
      intro F A p hr
      change (ThreeGames.interface g h).realizeFamily F (p.program ++ [.halt]) p.budget = A
      rw [MachineAdversaryInterface.realizeFamily_append_halt]
      exact hr }

noncomputable def signature (g₀ g₁ g₂ : ThreeGames.Game) : MultiSignature language where
  unary := {
    interpret := fun X => match X with
      | .endpoint => ThreeGames.object g₀ g₂
      | .left => ThreeGames.object g₀ g₁
      | .right => ThreeGames.object g₁ g₂
    certificate := by
      intro X Y e
      change Primitive X Y at e
      cases e
      cases X with
        | endpoint => exact appendCertificate g₀ g₂
        | left => exact appendCertificate g₀ g₁
        | right => exact appendCertificate g₁ g₂
    compiler_eq := by intro X Y e; change Primitive X Y at e; cases e; cases X <;> rfl }
  binary := fun e => match e with
    | .hybrid => ThreeGames.reduction g₀ g₁ g₂
  left_compiler := by intro _ _ _ e; cases e; rfl
  right_compiler := by intro _ _ _ e; cases e; rfl

@[macro_inline] def context (g₀ g₁ g₂ : ThreeGames.Game) : Context (signature g₀ g₁ g₂).unary :=
  [⟨.left, fun _ => ()⟩, ⟨.right, fun _ => ()⟩]

/-- Public constructors erase the noncomputable game semantics. The right
branch has an observable syntax change without changing its adversary. -/
@[macro_inline] def derivation (g₀ g₁ g₂ : ThreeGames.Game) :
    MultiDerivation (signature g₀ g₁ g₂) (context g₀ g₁ g₂) .endpoint (fun _ => ()) :=
  MultiDerivation.binary (L := language) (S := signature g₀ g₁ g₂)
    (Γ := context g₀ g₁ g₂) Binary.hybrid (fun _ => ())
    (MultiDerivation.hypothesis (S := signature g₀ g₁ g₂) (Γ := context g₀ g₁ g₂)
      ⟨0, by change 0 < 2; decide⟩)
    (MultiDerivation.transport (S := signature g₀ g₁ g₂) (Γ := context g₀ g₁ g₂)
      (ReductionExpr.primitive (L := language.unary) (Primitive.append Object.right))
      (fun _ => ())
      (MultiDerivation.hypothesis (S := signature g₀ g₁ g₂) (Γ := context g₀ g₁ g₂)
        ⟨1, by change 1 < 2; decide⟩))

/-- Two different probabilistic experiments and an intermediate fair sample. -/
def firstGame : ThreeGames.Game := fun _ A => A false
noncomputable def middleGame : ThreeGames.Game := fun _ A => sampleBit.bind A
def lastGame : ThreeGames.Game := fun _ A => A true

set_option backward.isDefEq.respectTransparency false in
def sourceSize : (ThreeGames.interface firstGame lastGame).InputSizeBound (fun _ => ()) where
  limit n := n + 5
  length_le := by
    intro n request
    rw [MachineAdversaryInterface.machineInput_length]
    simp [ThreeGames.interface, FiniteBitEncoding.unit, FiniteBitEncoding.bool]

noncomputable def sourceWitness : (ThreeGames.object firstGame lastGame).Witness (fun _ => ())
    ((ThreeGames.interface firstGame lastGame).realizeFamily (fun _ => ()) randomOutputBit (fun _ => 2)) where
  bounded := ⟨randomOutputBit, fun _ => 2, PolynomiallyBounded.const 2, randomOutputBit_haltsWithin_any⟩
  realizes := rfl
  admissible := ⟨randomOutputBit, fun _ => 2, sourceSize, PolynomiallyBounded.const 2,
    randomOutputBit_haltsWithin_any,
    PolynomiallyBounded.id.add (PolynomiallyBounded.const 5), rfl⟩

example (m : Nat) :
    ((ThreeGames.reduction firstGame middleGame lastGame).left.mapWitness sourceWitness).bounded.budget m = 2 := rfl
example (m : Nat) :
    ((ThreeGames.reduction firstGame middleGame lastGame).right.mapWitness sourceWitness).bounded.budget m = 2 := rfl

@[macro_inline] def replacement (g₀ g₁ g₂ : ThreeGames.Game)
    (i : Fin (context g₀ g₁ g₂).length) :
    MultiDerivation (signature g₀ g₁ g₂) (context g₀ g₁ g₂)
      ((context g₀ g₁ g₂)[i]).object ((context g₀ g₁ g₂)[i]).family where
  plan := if i.val = 0 then .hypothesis i else .unary (.suffix [.halt]) (.hypothesis i)
  compilers := if i.val = 0 then [(i, .identity)] else [(i, .comp (.suffix [.halt]) .identity)]
  emitted_eq := by intro p; split_ifs <;> rfl
  typed := by
    rcases i with ⟨n, h⟩
    rcases n with _ | n
    · exact ⟨MultiTree.hypothesis (S := signature g₀ g₁ g₂) (Γ := context g₀ g₁ g₂) ⟨0, h⟩, rfl⟩
    · rcases n with _ | n
      · exact ⟨MultiTree.transport (S := signature g₀ g₁ g₂) (Γ := context g₀ g₁ g₂)
          (ReductionExpr.primitive (L := language.unary) (Primitive.append Object.right))
          (fun _ => ())
          (MultiTree.hypothesis (S := signature g₀ g₁ g₂) (Γ := context g₀ g₁ g₂) ⟨1, h⟩), rfl⟩
      · change n + 2 < 2 at h
        omega

/-- info: true -/
#guard_msgs in
#eval
  let output := (derivation firstGame middleGame lastGame).run randomOutputBit
  output.map (fun (i, _) => i) == [0, 1] &&
    output.map (fun (_, p) => p) == [randomOutputBit, randomOutputBit ++ [.halt]]

/-- info: true -/
#guard_msgs in
#eval
  let output := ((derivation firstGame middleGame lastGame).substitute
    (fun i => replacement firstGame middleGame lastGame i)).run randomOutputBit
  output.map (fun (i, _) => i) == [0, 1] &&
    output.map (fun (_, p) => p) == [randomOutputBit, randomOutputBit ++ [.halt, .halt]]

example (g₀ g₁ g₂ : ThreeGames.Game)
    (h : (context g₀ g₁ g₂).Valid) :
    (ThreeGames.object g₀ g₂).Secure (fun _ => ()) := (derivation g₀ g₁ g₂).sound h

example (g₀ g₁ g₂ : ThreeGames.Game) : (derivation g₀ g₁ g₂).extract.length = 2 := by
  have h := congrArg List.length (derivation g₀ g₁ g₂).extract_compilers
  have hp : (derivation g₀ g₁ g₂).plan.paths.length = 2 := by rfl
  have h' : (derivation g₀ g₁ g₂).extract.length = (derivation g₀ g₁ g₂).plan.paths.length := by
    simpa only [List.length_map] using h
  exact h'.trans hp

example (g₀ g₁ g₂ : ThreeGames.Game)
    (h₀₁ : (ThreeGames.object g₀ g₁).Secure (fun _ => ()))
    (h₁₂ : (ThreeGames.object g₁ g₂).Secure (fun _ => ())) :
    (ThreeGames.object g₀ g₂).Secure (fun _ => ()) := ThreeGames.secure _ _ _ _ h₀₁ h₁₂

example (g₀ g₁ g₂ : ThreeGames.Game) (p : BoundedProgram) (m : Nat) :
    (ThreeGames.reduction g₀ g₁ g₂).left.budget p m = p.budget m ∧
      (ThreeGames.reduction g₀ g₁ g₂).right.budget p m = p.budget m := ⟨rfl, rfl⟩

example : (ThreeGames.goal firstGame lastGame).advantage 0 () (fun b => PMF.pure b) = 1 := by
  simp [ThreeGames.goal, firstGame, lastGame, eventProb, probabilityGap]

example : (ThreeGames.goal firstGame firstGame).advantage 0 () (fun b => PMF.pure b) = 0 := by
  simp [ThreeGames.goal, firstGame, eventProb, probabilityGap]

example : (ThreeGames.goal lastGame lastGame).advantage 0 () (fun b => PMF.pure b) = 0 := by
  simp [ThreeGames.goal, lastGame, eventProb, probabilityGap]

example (p : BoundedProgram) (input : List Bool)
    (leaf : BranchLeaf (context firstGame middleGame lastGame) Object.endpoint (fun _ => ())) :
    HaltsWithin (leaf.transform.compiler.run p.program) input
      (leaf.transform.budget p input.length) := leaf.halts p input

/- Substitution keeps repeated occurrences; the leaf compilers run in the
correct order even when both branches refer to the same final assumption. -/
private def repeated : CompilerTree 2 :=
  .binary (.suffix [.halt]) (.constant [.halt]) (.hypothesis 0) (.hypothesis 1)
private def replacements : Fin 2 → CompilerTree 1 := fun _ =>
  .unary (.suffix [.halt]) (.hypothesis 0)

/-- info: true -/
#guard_msgs in
#eval
  let output := (repeated.substitute replacements).run randomOutputBit
  output.map (fun (i, _) => i.val) == [0, 0] &&
    output.map (fun (_, p) => p) == [randomOutputBit ++ [.halt, .halt], [.halt, .halt]]

example (p : Program) : (repeated.substitute replacements).run p =
    (repeated.run p).flatMap (fun (i, q) => (replacements i).run q) :=
  repeated.run_substitute replacements p

/- Zero gap on one edge cannot justify the endpoint gap. Reversing the
intermediate experiment shows why neither edge may simply be discarded. -/
example : ¬ probabilityGap (0 : ℝ≥0∞) 1 ≤ probabilityGap 0 0 := by
  simp [probabilityGap]
example : ¬ probabilityGap (0 : ℝ≥0∞) 1 ≤ probabilityGap 1 1 := by
  simp [probabilityGap]

end CryptoLogic.MultiExamples
