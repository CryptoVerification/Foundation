import Foundation.Crypto.Logic.General.Legacy
import Foundation.Examples.PRGEncryption
import Foundation.Examples.WholeOracleAttack
import Foundation.Examples.CryptoLogic
import Foundation.Examples.MultiAssumption

namespace CryptoLogic.General.Examples

open Backends Foundation.Symmetric
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

-- A masking target cannot be supplied to an interactive source compiler.
#check_failure Compiler.comp (K := system)
  (Compiler.primitive (Primitive.mask true))
  (Compiler.primitive (Primitive.interactive .identity))

-- The cross-machine compiler has a computable syntax encoding.
/-- info: true -/
#guard_msgs in
#eval match Encodable.decode (α := Primitive Kind.native Kind.masking)
    (Encodable.encode (Primitive.mask true)) with
  | some (.mask side) => side
  | none => false

inductive Object where
  | plain | masked | oracleSource | oracleTarget
  deriving DecidableEq, Repr

def machine : Object → Kind
  | .plain => .native
  | .masked => .masking
  | .oracleSource | .oracleTarget => .interactive

inductive Unary : Object → Object → Type where
  | relax : Unary .oracleSource .oracleTarget

/-- A deliberately redundant branch checks heterogeneous outputs without
asserting a new cryptographic theorem: the source assumption is retained. -/
inductive Binary : Object → Object → Object → Type where
  | retainAndMask : Binary .plain .plain .masked

abbrev language : Language system where
  Object := Object
  machine := machine
  Unary := Unary
  unaryCompiler := fun e => match e with | .relax => .primitive (.interactive .identity)
  Binary := Binary
  binaryCompilers := fun e => match e with | .retainAndMask => (Compiler.identity (K := system) Kind.native, .primitive (.mask true))

abbrev G := Foundation.Symmetric.Examples.testGenerator

def time : Nat → Nat := fun _ => 2

noncomputable def objects : ∀ X : Object, General.SecurityObject system (machine X)
  | .plain => prgNativeObject G time
  | .masked => prgMaskingObject G (G.reductionTime time)
  | .oracleSource => interactiveObject CryptoOracle.Examples.wholeInterface (fun _ => 25) (fun _ => 2)
  | .oracleTarget => interactiveObject CryptoOracle.Examples.wholeInterface (fun _ => 100) (fun _ => 5)

noncomputable def retainAndMask : CertifiedBinaryReduction (objects .plain) (objects .plain) (objects .masked) where
  left := (CertifiedReduction.id (objects .plain)).toTransform
  right := PRG.transform G time true
  leftLoss := AdvantageBound.id
  rightLoss := AdvantageBound.id
  leftNegligible := AdvantageBound.id_preservesNegligible
  rightNegligible := AdvantageBound.id_preservesNegligible
  advantage_le := by intro F A n; exact le_self_add

noncomputable def signature : Signature language where
  interpret := objects
  unary := fun e => match e with
    | .relax => Interactive.reduction CryptoOracle.Examples.wholeRelax AdvantageBound.id_preservesNegligible
  unary_compiler := by intro X Y e; cases e; rfl
  binary := fun e => match e with | .retainAndMask => retainAndMask
  left_compiler := by intro X Y Z e; cases e; rfl
  right_compiler := by intro X Y Z e; cases e; rfl

def family : InstanceFamily G.encryptionGoal := fun _ => Foundation.Symmetric.Examples.testMessages

def mixedContext : Context signature where
  length := 2
  claim i := if i.val = 0 then ⟨.plain, family⟩ else ⟨.masked, family⟩

@[macro_inline] def mixed : Derivation signature mixedContext .plain family :=
  Derivation.binary (S := signature) Binary.retainAndMask family
    (Derivation.hypothesis (S := signature) (Γ := mixedContext) ⟨0, by decide⟩)
    (Derivation.hypothesis (S := signature) (Γ := mixedContext) ⟨1, by decide⟩)

/-- Only finite backend tags and finite code are inspected here. -/
def summary : Sigma system.Code → Kind × Bool × Nat
  | ⟨.native, code⟩ => (.native, false, code.length)
  | ⟨.masking, .native code⟩ => (.masking, false, code.length)
  | ⟨.masking, .masked side code⟩ => (.masking, side, code.length)
  | ⟨.interactive, code⟩ => (.interactive, false, code.length)

/-- info: true -/
#guard_msgs in
#eval (mixed.run [.randomBit .output, .halt]).map (fun (i, code) => (i, summary code)) ==
  [(0, Kind.native, false, 2), (1, Kind.masking, true, 2)]

/-- No semantic signature is evaluated when substituting and emitting code. -/
@[macro_inline] def replacement (i : Fin mixedContext.length) :
    Derivation signature mixedContext (mixedContext.claim i).object (mixedContext.claim i).family :=
  Derivation.transport (S := signature) (Γ := mixedContext)
    (.identity (mixedContext.claim i).object) (mixedContext.claim i).family
    (Derivation.hypothesis (S := signature) (Γ := mixedContext) i)

@[macro_inline] def substituted := mixed.substitute replacement

/-- info: true -/
#guard_msgs in
#eval
  (substituted.run [.randomBit .output, .halt]).map (fun (i, c) => (i, summary c)) ==
    (mixed.run [.randomBit .output, .halt]).map (fun (i, c) => (i, summary c))

noncomputable def sourceWitness : (objects .plain).Witness family (fun _ _ => Foundation.Probability.sampleBit) :=
  PRG.nativeWitness (Foundation.Symmetric.Examples.randomWitness G family)

/-- The source and both targets are concretely inhabited. -/
example : (objects .plain).adversaries.admissible family (fun _ _ => Foundation.Probability.sampleBit) :=
  sourceWitness.admissible

example : (retainAndMask.right.mapWitness family _ sourceWitness).code =
    .masked true [.randomBit .output, .halt] := rfl

example : (objects .masked).execution.ExecutesWithin family
    (.masked true [.randomBit .output, .halt]) () :=
  retainAndMask.right.compiler_executes family _ sourceWitness

example (h : mixedContext.Valid) : (objects .plain).Secure family := mixed.sound h

example : mixed.extract.map (fun leaf => leaf.index.val) = [0, 1] := by
  have h := congrArg (List.map (fun entry => entry.1.val)) mixed.extract_compilers
  simpa [mixed, Derivation.binary, Plan.paths, Derivation.hypothesis, BranchLeaf.packedCompiler, List.map_map, Function.comp_def, mixedContext, machine] using h

def oracleContext : Context signature where
  length := 1
  claim _ := ⟨.oracleTarget, fun _ => ()⟩

@[macro_inline] def oracle : Derivation signature oracleContext .oracleSource (fun _ => ()) :=
  Derivation.transport (S := signature) (.primitive Unary.relax) (fun _ => ())
    (Derivation.hypothesis (S := signature) (Γ := oracleContext) ⟨0, by decide⟩)

/-- info: true -/
#guard_msgs in
#eval (oracle.run CryptoOracle.Examples.adaptiveCode).map (fun (i, code) => (i, summary code)) ==
  [(0, Kind.interactive, false, 4)]

noncomputable def oracleWitness : (objects .oracleSource).Witness
    (fun _ => ()) (fun _ => CryptoOracle.Examples.adaptive) :=
  Interactive.witness CryptoOracle.Examples.adaptiveWholeWitness

example : ((signature.unary Unary.relax).mapWitness _ _ oracleWitness).code =
    CryptoOracle.Examples.adaptiveCode := rfl

example : (objects .oracleTarget).execution.ExecutesWithin (fun _ => ())
    CryptoOracle.Examples.adaptiveCode () :=
  (signature.unary Unary.relax).toTransform.compiler_executes _ _ oracleWitness

/-- The existing unary API emits exactly the same native code after conversion. -/
@[macro_inline] def oldUnary := Legacy.Unary.derivation CryptoLogic.Examples.derivation

/-- info: true -/
#guard_msgs in
#eval
  (oldUnary.run Machine.Examples.randomOutputBit).map (fun (i, c) => (i, summary c)) ==
    [(1, Kind.native, false, 1)]

example (code : Machine.Program) : oldUnary.run code =
    [(CryptoLogic.Examples.derivation.code.selected.val,
      ⟨Kind.native, CryptoLogic.Examples.derivation.compiler.run code⟩)] :=
  Legacy.Unary.derivation_run CryptoLogic.Examples.derivation code

/-- Existing binary derivations retain branch order and source code exactly. -/
@[macro_inline] def oldMulti := Legacy.derivation
  (CryptoLogic.MultiExamples.derivation CryptoLogic.MultiExamples.firstGame
    CryptoLogic.MultiExamples.middleGame CryptoLogic.MultiExamples.lastGame)

/-- info: true -/
#guard_msgs in
#eval
  (oldMulti.run Machine.Examples.randomOutputBit).map (fun (i, c) => (i, summary c)) ==
    [(0, Kind.native, false, 2), (1, Kind.native, false, 3)]

end CryptoLogic.General.Examples
