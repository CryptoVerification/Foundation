import Foundation.Machine.SavedSamplerLayout
import Foundation.Machine.ScalarSamplePadding

namespace Machine.ScalarSamplerContinuation

/-- The actual retry block followed by physical fixed-width padding and a
charged caller halt. This intermediate code retains the saved width counter. -/
def program : Program := RejectionSampling.program.followedBy ScalarSamplePadding.program

def entry : Nat := RejectionSampling.program.length+1

def exit : Nat := RejectionSampling.program.length+ScalarSamplePadding.program.length+2

private def pre : Program := RejectionSampling.program.asSubroutine 0 entry

private theorem padding_layout : program =
    Program.withSubroutine pre ScalarSamplePadding.program [.halt] exit := by
  simp [program, Program.followedBy, Program.withSubroutine, pre, entry, exit, List.append_assoc]

private theorem eval_halted (p : Program) (c : Configuration) (steps : Nat)
    (h : c.halted = true) : evalConfigWithin p c steps = PMF.pure c := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [evalConfigWithin, ih, stepPMF, next, h]

/-- Every accepted physical layout returns its padded scalar code within
one common charged budget. The caller's random instructions elsewhere do
not introduce randomness into this deterministic continuation. -/
theorem continuation_eval (width : Nat) (modulus sample : List Bool)
    (hModulus : modulus.length ≤ width) (hSample : sample.length ≤ width)
    (accepted : Configuration)
    (hInput : accepted.inputTape.Equivalent
      {left := modulus.reverse.map some ++ none::List.replicate width (some true)})
    (hOutput : accepted.outputTape.Equivalent {left := sample.reverse.map some}) :
    ∃ finish : Configuration, finish.halted = true ∧
      finish.outputBits = Binary.encode width (Binary.value sample) ∧
      ∀ extra : Nat, evalConfigWithin program (accepted.resumeAt entry)
        (13*width+18+extra) = PMF.pure finish := by
  obtain ⟨padded, hHalt, hBits, hEval⟩ := ScalarSamplePadding.eval_from_layout width modulus sample
    hModulus hSample (accepted.resumeAt 0) rfl rfl hInput hOutput
  have stopped (target : Configuration)
      (trace : PaddedRunsFor ScalarSamplePadding.program (accepted.resumeAt 0) target (13*width+17)) :
      target.halted = true := by
    have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
    rw [hEval] at member
    have same : target = padded := by simpa using member
    exact same ▸ hHalt
  have call := Program.evalConfigWithin_withSubroutine_final_halt pre ScalarSamplePadding.program
    (accepted.resumeAt 0) (Nat.zero_le _) rfl (13*width+17) stopped
  dsimp only at call
  rw [hEval, PMF.pure_map] at call
  have exitEq : pre.length+ScalarSamplePadding.program.length+1 = exit := by
    simp only [pre, Program.asSubroutine_length, entry, exit]
    omega
  rw [exitEq, ← padding_layout] at call
  have actual : evalConfigWithin program (accepted.resumeAt entry) (13*width+18) =
      PMF.pure {padded with pc := exit, halted := true} := by
    simpa [pre, Program.asSubroutine_length, entry,
      Configuration.rebasePc, Configuration.resumeAt, Nat.add_assoc] using call
  refine ⟨{padded with pc := exit, halted := true}, rfl, hBits, ?_⟩
  intro extra
  rw [evalConfigWithin_add, actual, PMF.pure_bind, eval_halted _ _ extra rfl]

end Machine.ScalarSamplerContinuation
