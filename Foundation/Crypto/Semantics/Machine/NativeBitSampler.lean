import Foundation.Crypto.Semantics.Machine.PrivateBitGeneration
import Foundation.Crypto.Semantics.Machine.NativeFirstArrival

/-! The existing six-instruction one-time-pad key generator as a reusable
closed native component. Width is marker data, never generated code. -/
namespace Machine.NativeBitSampler
open Foundation.Probability Foundation.Symmetric TimedExecution
set_option backward.isDefEq.respectTransparency false

theorem closed (start target : Configuration) (inside : start.pc < OneTimePad.keygen.length)
    (actual : Step OneTimePad.keygen start target) (active : target.halted = false) :
    target.pc < OneTimePad.keygen.length := by
  have running : start.halted = false := by
    cases h : start.halted
    · rfl
    · exact False.elim ((no_step_of_halted h) actual)
  have pc : start.pc < 6 := inside
  interval_cases h : start.pc <;>
    simp [Step, successors, next, running, OneTimePad.keygen, h,
      Instruction.next, Configuration.advance, Configuration.updateTape] at actual
  all_goals
    first
    | subst target; simp_all [OneTimePad.keygen]; split <;> decide
    | subst target; simp_all [OneTimePad.keygen]
    | rcases actual with rfl | rfl <;> simp [OneTimePad.keygen]

noncomputable def component (width : Nat) : NativeComponent Unit (Bits width) where
  procedure := PrivateBitGeneration.native width
  closed := closed
  entry := fun _ => by change 0 < 6; decide
  active := fun _ => rfl
  halted := fun _ _ _ => rfl

theorem code (width : Nat) : (component width).procedure.code = OneTimePad.keygen := rfl

theorem semantics (width : Nat) :
    (component width).procedure.execution.semantics () = uniform (Bits width) := rfl

theorem budget (width : Nat) :
    (component width).procedure.execution.budget () = 5 * width + 2 := rfl

/-- Adjacent pre-halt law, including width zero. The only remaining step is
an ordinary halt; no generated key or tape is replaced by an observer. -/
theorem before_halt (width : Nat) (pastInput pastKey : List Bool) :
    evalConfigWithin OneTimePad.keygen
      (OneTimePad.state pastInput pastKey (List.replicate width true)) (5 * width + 1) =
    (uniform (Bits width)).map (fun key =>
      { OneTimePad.finish 5 (pastInput ++ List.replicate width true) (pastKey ++ key.toList)
        with halted := false }) := by
  induction width generalizing pastInput pastKey with
  | zero =>
      simp [evalConfigWithin, stepPMF, next, OneTimePad.keygen, OneTimePad.state,
        OneTimePad.finish, Tape.ofBits, Instruction.next, Configuration.tape,
        Bits.toList, PMF.map_const, Function.const_def]
  | succ width ih =>
      rw [List.replicate_succ, show 5 * (width + 1) + 1 = 5 + (5 * width + 1) by omega,
        evalConfigWithin_add, OneTimePad.keygen_iteration, PMF.bind_map]
      simp only [Function.comp_def, ih]
      rw [← uniform_bits_cons]
      simp [PMF.map_bind, PMF.map_comp, Function.comp_def, Bits.toList,
        List.ofFn_succ, List.append_assoc]

end Machine.NativeBitSampler
