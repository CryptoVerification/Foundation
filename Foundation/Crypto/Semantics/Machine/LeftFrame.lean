import Foundation.Crypto.Semantics.Machine.NativeFirstArrival

/-! Exact saved-cell frames for programs that never move a head left.
Arbitrary represented cells may be appended on the left of either tape.
They are retained, including redundant blanks, with identical probabilities
and actual first-halt times. This changes the entry precondition, not code. -/
namespace Machine
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def Tape.frameLeft (frame : List (Option Bool)) (tape : Tape) : Tape :=
  {tape with left := tape.left ++ frame}

def Configuration.frameLeft (inputFrame outputFrame : List (Option Bool)) (state : Configuration) : Configuration :=
  { pc := state.pc
    inputTape := state.inputTape.frameLeft inputFrame
    outputTape := state.outputTape.frameLeft outputFrame
    halted := state.halted }

private def frameSuccessor (inputFrame outputFrame : List (Option Bool)) :
    Configuration ⊕ (Configuration × Configuration) → Configuration ⊕ (Configuration × Configuration)
  | .inl state => .inl (state.frameLeft inputFrame outputFrame)
  | .inr (first, second) => .inr (first.frameLeft inputFrame outputFrame, second.frameLeft inputFrame outputFrame)

theorem Instruction.next_frameLeft (instruction : Instruction) (state : Configuration)
    (noLeft : ∀ tape, instruction ≠ .moveLeft tape) (inputFrame outputFrame : List (Option Bool)) :
    instruction.next (state.frameLeft inputFrame outputFrame) =
      frameSuccessor inputFrame outputFrame (instruction.next state) := by
  cases instruction with
  | halt => rfl
  | jump pc => rfl
  | moveLeft tape => exact False.elim (noLeft tape rfl)
  | moveRight tape =>
      cases tape <;>
        simp [Instruction.next, Configuration.frameLeft, Tape.frameLeft, Configuration.updateTape,
          Configuration.advance, Tape.moveRight]
      all_goals split <;> simp [frameSuccessor, Configuration.frameLeft, Tape.frameLeft, List.cons_append]
  | write tape bit => cases tape <;> rfl
  | erase tape => cases tape <;> rfl
  | randomBit tape => cases tape <;> rfl
  | branch tape blankPc zeroPc onePc => cases tape <;> rfl

theorem next_frameLeft (code : Program) (state : Configuration)
    (noLeft : ∀ tape, Instruction.moveLeft tape ∉ code) (inputFrame outputFrame : List (Option Bool)) :
    next code (state.frameLeft inputFrame outputFrame) =
      (next code state).map (frameSuccessor inputFrame outputFrame) := by
  cases hHalted : state.halted with
  | true => simp [next, Configuration.frameLeft, hHalted]
  | false =>
      simp only [next, Configuration.frameLeft, hHalted, Bool.false_eq_true, ↓reduceIte]
      cases hInstruction : code[state.pc]? with
      | none => rfl
      | some instruction =>
          have hNoLeft : ∀ tape, instruction ≠ .moveLeft tape := by
            intro tape hEq
            apply noLeft tape
            rw [← hEq]
            exact List.mem_of_getElem? hInstruction
          simpa only [Configuration.frameLeft, hHalted, Option.map_some] using
            congrArg some (Instruction.next_frameLeft instruction state hNoLeft inputFrame outputFrame)

theorem stepPMF_frameLeft (code : Program) (state : Configuration)
    (noLeft : ∀ tape, Instruction.moveLeft tape ∉ code) (inputFrame outputFrame : List (Option Bool)) :
    stepPMF code (state.frameLeft inputFrame outputFrame) =
      (stepPMF code state).map (Configuration.frameLeft inputFrame outputFrame) := by
  simp only [stepPMF, next_frameLeft code state noLeft inputFrame outputFrame]
  cases hNext : next code state with
  | none => simp [PMF.pure_map]
  | some result =>
      cases result with
      | inl target => simp [frameSuccessor, PMF.pure_map]
      | inr pair =>
          rcases pair with ⟨first, second⟩
          simp only [Option.map_some, frameSuccessor, PMF.map_comp]
          congr 1
          funext bit
          cases bit <;> rfl

theorem evalConfigWithin_frameLeft (code : Program) (state : Configuration)
    (noLeft : ∀ tape, Instruction.moveLeft tape ∉ code) (inputFrame outputFrame : List (Option Bool)) (fuel : Nat) :
    evalConfigWithin code (state.frameLeft inputFrame outputFrame) fuel =
      (evalConfigWithin code state fuel).map (Configuration.frameLeft inputFrame outputFrame) := by
  rw [← timed_eval_eq, ← timed_eval_eq]
  exact (eval_map (stepPMF code) (stepPMF code) (Configuration.frameLeft inputFrame outputFrame)
    (fun state => (stepPMF_frameLeft code state noLeft inputFrame outputFrame).symm) fuel state).symm

theorem runToHalt_frameLeft (code : Program) (state : Configuration)
    (noLeft : ∀ tape, Instruction.moveLeft tape ∉ code) (inputFrame outputFrame : List (Option Bool)) (fuel : Nat) :
    runToBoundary (stepPMF code) Configuration.halted fuel (state.frameLeft inputFrame outputFrame) =
      (runToBoundary (stepPMF code) Configuration.halted fuel state).map
        (fun result => (result.1.frameLeft inputFrame outputFrame, result.2)) := by
  exact runToBoundary_map (stepPMF code) (stepPMF code) Configuration.halted Configuration.halted
    (Configuration.frameLeft inputFrame outputFrame) (fun _ => rfl)
    (fun state _ => stepPMF_frameLeft code state noLeft inputFrame outputFrame) fuel state

end Machine
