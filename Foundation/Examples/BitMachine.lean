import Foundation.Machine.Basic

namespace Machine.Examples

/-- One operational step executes the halt instruction. -/
def haltImmediately : Program := [.halt]

example : Step haltImmediately (Configuration.initial [])
    { (Configuration.initial []) with halted := true } := by decide

/-- Branch on the first input cell and write that bit on the output tape. -/
def copyOneBit : Program :=
  [.branch .input 5 1 3,
   .write .output false, .jump 5,
   .write .output true, .jump 5,
   .halt]

/-- The same finite control with the two output bits exchanged. -/
def negateOneBit : Program :=
  [.branch .input 5 1 3,
   .write .output true, .jump 5,
   .write .output false, .jump 5,
   .halt]

/-- These checks inspect actual small-step chains, including the halt step. -/
example : ∃ c₁ c₂ c₃ c₄,
    Step copyOneBit (Configuration.initial [true]) c₁ ∧
    Step copyOneBit c₁ c₂ ∧ Step copyOneBit c₂ c₃ ∧
    Step copyOneBit c₃ c₄ ∧
    c₄.halted = true ∧ c₄.outputBits = [true] := by
  refine ⟨{ pc := 3, inputTape := Tape.ofBits [true] },
    { pc := 4, inputTape := Tape.ofBits [true],
      outputTape := { current := some true } },
    { pc := 5, inputTape := Tape.ofBits [true],
      outputTape := { current := some true } },
    { pc := 5, inputTape := Tape.ofBits [true],
      outputTape := { current := some true }, halted := true }, ?_⟩
  decide

example : ∃ c₁ c₂ c₃ c₄,
    Step negateOneBit (Configuration.initial [true]) c₁ ∧
    Step negateOneBit c₁ c₂ ∧ Step negateOneBit c₂ c₃ ∧
    Step negateOneBit c₃ c₄ ∧
    c₄.halted = true ∧ c₄.outputBits = [false] := by
  refine ⟨{ pc := 3, inputTape := Tape.ofBits [true] },
    { pc := 4, inputTape := Tape.ofBits [true],
      outputTape := { current := some false } },
    { pc := 5, inputTape := Tape.ofBits [true],
      outputTape := { current := some false } },
    { pc := 5, inputTape := Tape.ofBits [true],
      outputTape := { current := some false }, halted := true }, ?_⟩
  decide

/-- A one-instruction fair random output bit, followed by halt. -/
def randomOutputBit : Program := [.randomBit .output, .halt]

example : successors randomOutputBit (Configuration.initial []) =
    [{ pc := 1, outputTape := { current := some false } },
     { pc := 1, outputTape := { current := some true } }] := rfl

def randomNext (b : Bool) : Configuration :=
  { pc := 1, outputTape := { current := some b } }

theorem randomOutputBit_stepPMF :
    stepPMF randomOutputBit (Configuration.initial []) =
      Foundation.Probability.sampleBit.map randomNext := by
  change Foundation.Probability.sampleBit.map
      (fun b => if b then
        ({ pc := 1, outputTape := { current := some true } } : Configuration)
        else ({ pc := 1, outputTape := { current := some false } } : Configuration)) = _
  congr 1
  funext b
  cases b <;> rfl

example : Foundation.Probability.eventProb
    (stepPMF randomOutputBit (Configuration.initial []))
    (fun c => c.outputBits = [true]) = 1 / 2 := by
  rw [randomOutputBit_stepPMF]
  unfold Foundation.Probability.eventProb
  rw [PMF.toOuterMeasure_map_apply]
  have hpre : (randomNext ⁻¹' {c : Configuration | c.outputBits = [true]}) =
      {true} := by
    ext b
    cases b <;> simp [randomNext, Configuration.outputBits, Tape.bits]
  rw [hpre]
  simp [Foundation.Probability.sampleBit, Foundation.Probability.uniform]

example : Program.encode copyOneBit = Program.encode copyOneBit := rfl

example (p q : Program) (h : Program.encode p = Program.encode q) : p = q :=
  Program.encode_injective h

end Machine.Examples
