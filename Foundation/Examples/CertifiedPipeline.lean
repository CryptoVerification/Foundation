import Foundation.Crypto.Meta.General.CertifiedPipeline
import Foundation.Crypto.Logic.General.Backends

/-! Variable-depth certified chains on the actual native machine. Appending
halts preserves all transitions, including random branches, for any protocol
adapter. Code length grows with depth while its time certificate is unchanged.
Parameter-indexed emitted syntax is not silently called a uniform program;
here an explicit elimination theorem supplies the original fixed program. -/
namespace CryptoLogic.General.CertifiedPipeline.Examples
open CryptoLogic.General.Backends
universe u v w
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
variable (X : CryptoLogic.SecurityObject.{u, v, w})

noncomputable def suffixHalt : CertifiedTransform (nativeObject X) (nativeObject X) where
  transform := ⟨fun I => I, fun _ A => A⟩
  compiler := .primitive (.native (.suffix [.halt]))
  mapWitness := fun F A W => {
    code := List.append (W.code : Machine.Program) [Machine.Instruction.halt]
    resources := W.resources
    executes := ⟨W.executes.1, fun input =>
      (Machine.haltsWithin_append_halt_iff W.code input (W.resources input.length)).mpr (W.executes.2 input)⟩
    realizes := by
      exact (Machine.MachineAdversaryInterface.realizeFamily_append_halt
        X.interface F W.code W.resources).trans W.realizes
    admissible := W.admissible }
  code_eq := by intros; rfl

noncomputable def stage (_i : Nat) := suffixHalt X

theorem emitted (program : Machine.Program) (depth : Nat) :
    (compiler (stage X) depth).run program = program ++ List.replicate depth Machine.Instruction.halt := by
  induction depth with
  | zero => simp only [compiler, Compiler.run, List.replicate_zero, List.append_nil]
  | succ depth ih =>
      change List.append ((compiler (stage X) depth).run program : Machine.Program) [Machine.Instruction.halt] = _
      rw [ih, List.replicate_succ']
      exact List.append_assoc _ _ _

/-- The depth may be any function; zero accumulated time overhead suffices. -/
theorem resources (input : Entry (nativeObject X)) (depth : Nat) :
    (run (stage X) input depth).witness.resources = input.witness.resources := by
  induction depth with
  | zero => rfl
  | succ depth ih => exact ih

theorem arbitrary_depth_polynomial (input : Entry (nativeObject X)) (depth : Nat → Nat) :
    PolynomiallyBounded (fun n => (run (stage X) input (depth n)).witness.resources n) := by
  have hInput : PolynomiallyBounded (fun n => input.witness.resources n) := input.witness.executes.1
  simpa only [resources] using hInput

/-- Even this zero-time-overhead family has nonconstant emitted syntax. This
is not an impossibility of a uniform semantic implementation: the original
program is one, as the following elimination theorem explicitly proves. -/
theorem emitted_not_constant (program : Machine.Program) :
    ¬ ∃ fixed : Machine.Program, ∀ depth, (compiler (stage X) depth).run program = fixed := by
  rintro ⟨fixed, h⟩
  have eq := (h 0).trans (h 1).symm
  rw [emitted, emitted] at eq
  have lengths := congrArg List.length eq
  simp only [List.length_append, List.length_replicate] at lengths
  omega

/-- Eliminate arbitrary many proof-introduced halt instructions without
changing the complete native distribution at any observation horizon. -/
theorem eliminate (program : Machine.Program) (depth : Nat) (input : List Bool) (fuel : Nat) :
    Machine.evalWithin ((compiler (stage X) depth).run program) input fuel =
      Machine.evalWithin program input fuel := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change Machine.evalWithin (List.append ((compiler (stage X) depth).run program : Machine.Program) [Machine.Instruction.halt]) input fuel = _
      exact (Machine.evalWithin_append_halt _ input fuel).trans ih

end CryptoLogic.General.CertifiedPipeline.Examples
