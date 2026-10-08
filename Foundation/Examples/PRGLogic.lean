import Foundation.Constructions.Symmetric.PRGLogic
import Foundation.Examples.PRGEncryption

namespace Foundation.Symmetric.LogicExamples

open CryptoLogic.General CryptoLogic.General.Backends
open Foundation.Probability Machine Generator
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

abbrev G := Examples.testGenerator
def time : Nat → Nat := fun _ => 14
def family : InstanceFamily G.encryptionGoal := fun _ => Examples.testMessages

/-- Extract only masking programs from the heterogeneous output list. -/
def programs (output : List (Nat × Sigma system.Code)) : List (Nat × Masking.Code) :=
  output.filterMap fun (i, code) => match code with
    | ⟨.masking, program⟩ => some (i, program)
    | _ => none

-- Two premises generate two distinct finite programs, without evaluating
-- noncomputable PRG game semantics or a stopping proof.
/-- info: true -/
#guard_msgs in
#eval programs ((Logic.derivation G time family).run Examples.testProgram) ==
  [(0, .masked false Examples.testProgram), (1, .masked true Examples.testProgram)]

-- Replacing the two positions with one assertion retains both occurrences.
/-- info: true -/
#guard_msgs in
#eval programs ((Logic.sharedDerivation G time family).run Examples.testProgram) ==
  [(0, .masked false Examples.testProgram), (0, .masked true Examples.testProgram)]

-- Run the emitted programs at their certified bound, including preprocessing.
/-- info: [(some false, 43), (some true, 43)] -/
#guard_msgs in
#eval (programs ((Logic.derivation G time family).run Examples.testProgram)).map fun (_, code) =>
  let (finish, used) := Masking.simulate code false (G.reductionTime time 0)
    (Masking.initial code Examples.testHeader [false, false] [true, false] [false, true])
  (Masking.result finish, used)

-- One fewer transition is insufficient for either emitted branch.
/-- info: [(none, 42), (none, 42)] -/
#guard_msgs in
#eval (programs ((Logic.derivation G time family).run Examples.testProgram)).map fun (_, code) =>
  let (finish, used) := Masking.simulate code false (G.reductionTime time 0 - 1)
    (Masking.initial code Examples.testHeader [false, false] [true, false] [false, true])
  (Masking.result finish, used)

/-- Kernel-checked equality of outputs, including arbitrary source code. -/
example (G : Generator) (t : Nat → Nat) (F : InstanceFamily G.encryptionGoal) (p : Program) :
    (Logic.sharedDerivation G t F).run p =
      [(0, ⟨Kind.masking, .masked false p⟩), (0, ⟨Kind.masking, .masked true p⟩)] :=
  Logic.shared_run G t F p

example (G : Generator) (t : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (h : SecureOnWithin G.prgGoal (G.challengeClass (G.reductionTime t)) F) :
    SecureOnWithin G.encryptionGoal (G.nativeClass t) F := Logic.secure G t F h

example (G : Generator) (t : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (ε₀ ε₁ : Nat → ℝ≥0∞)
    (h₀ : BoundedByOnWithin G.prgGoal (G.challengeClass (G.reductionTime t)) F ε₀)
    (h₁ : BoundedByOnWithin G.prgGoal (G.challengeClass (G.reductionTime t)) F ε₁) :
    BoundedByOnWithin G.encryptionGoal (G.nativeClass t) F (fun n => ε₀ n + ε₁ n) :=
  Logic.bounded G t F ε₀ ε₁ h₀ h₁

example (G : Generator) (t : Nat → Nat) (F : InstanceFamily G.encryptionGoal)
    (ε : Nat → ℝ≥0∞)
    (h : BoundedByOnWithin G.prgGoal (G.challengeClass (G.reductionTime t)) F ε) :
    BoundedByOnWithin G.encryptionGoal (G.nativeClass t) F (fun n => 2 * ε n) :=
  Logic.bounded_twice G t F ε h

-- The classes are inhabited by one fixed randomized code for every G and F.
noncomputable def witness (G : Generator) (F : InstanceFamily G.encryptionGoal) :
    G.NativeWitness (fun _ => 2) F (fun _ _ => sampleBit) := Examples.randomWitness G F

example (G : Generator) (F : InstanceFamily G.encryptionGoal) (side : Bool)
    (n : Nat) (challenge : Bits (G.outputLength n)) :
    Masking.HaltsWithin (Masking.compile side (witness G F).program)
      (Masking.initial (Masking.compile side (witness G F).program) (G.header n (F n))
        (F n).1.toList (F n).2.toList challenge.toList)
      (G.reductionTime (fun _ => 2) n) :=
  Logic.emitted_halts G (fun _ => 2) side F _ (witness G F) n challenge

example (G : Generator) (F : InstanceFamily G.encryptionGoal) (side : Bool)
    (n : Nat) (challenge : Bits (G.outputLength n)) :
    Masking.output (Masking.compile side (witness G F).program)
      (Masking.initial (Masking.compile side (witness G F).program) (G.header n (F n))
        (F n).1.toList (F n).2.toList challenge.toList)
      (G.reductionTime (fun _ => 2) n) = sampleBit.map some :=
  Logic.emitted_output G (fun _ => 2) side F _ (witness G F) n challenge

example (G : Generator) (t : Nat → Nat) (F : InstanceFamily G.encryptionGoal) :
    (Logic.derivation G t F).extract.length = 2 := by
  have h := congrArg List.length ((Logic.derivation G t F).extract_compilers)
  have hp : (Logic.derivation G t F).plan.paths.length = 2 := rfl
  simpa only [List.length_map, hp] using h

example (G : Generator) (t : Nat → Nat) (F : InstanceFamily G.encryptionGoal) :
    (Logic.sharedDerivation G t F).extract.map (fun leaf => leaf.index.val) = [0, 0] := by
  have h := congrArg (List.map (fun entry => entry.1.val))
    ((Logic.sharedDerivation G t F).extract_compilers)
  have hp : (Logic.sharedDerivation G t F).plan.paths.map (fun entry => entry.1.val) = [0, 0] := rfl
  rw [hp] at h
  simpa only [List.map_map, Function.comp_def, BranchLeaf.packedCompiler] using h

end Foundation.Symmetric.LogicExamples
