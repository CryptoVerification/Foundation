import Foundation.Crypto.Semantics.Machine.NativeBitDecisionTree
import Foundation.Crypto.Semantics.Machine.NativeSequence

/-! Sequential native execution under uniform all-tape stopping contracts. -/
namespace Machine.NativeUniformSequence
open Foundation.Probability NativeBitDecisionTree

def StopsEverywhere (p : Program) (T : ℕ) : Prop := ∀ input output, Stops p input output T

theorem code_length (first second : Program) :
    (first.followedBy second).length = first.length + second.length + 3 := by
  simp [Program.followedBy]
  omega

theorem run (first second : Program) (T U : ℕ)
    (hFirst : StopsEverywhere first T) (hSecond : StopsEverywhere second U)
    (input output : Tape) :
    evalConfigWithin (first.followedBy second) (NativeBitChoice.start input output) (T + U + 1) =
      (evalConfigWithin first (NativeBitChoice.start input output) T).bind
        (fun c => (evalConfigWithin second (c.resumeAt 0) U).map
          (fun d => {d with pc := first.length + second.length + 2, halted := true})) := by
  have h := Program.evalConfigWithin_twoStages_configuration first second
    (NativeBitChoice.start input output) rfl rfl T U (hFirst input output)
    (by
      intro c _ d trace
      exact hSecond c.inputTape c.outputTape d trace)
  simpa [Program.followedBy, Program.withSubroutine,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem stops (first second : Program) (T U : ℕ)
    (hFirst : StopsEverywhere first T) (hSecond : StopsEverywhere second U) :
    StopsEverywhere (first.followedBy second) (T + U + 1) := by
  intro input output finish trace
  have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  rw [run first second T U hFirst hSecond input output, PMF.mem_support_bind_iff] at member
  obtain ⟨c, _, hc⟩ := member
  rw [PMF.mem_support_map_iff] at hc
  obtain ⟨d, _, rfl⟩ := hc
  rfl

end Machine.NativeUniformSequence
