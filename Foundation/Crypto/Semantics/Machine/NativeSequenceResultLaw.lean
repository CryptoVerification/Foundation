import Foundation.Crypto.Semantics.Machine.NativeUniformSequence

namespace Machine.NativeSequenceResultLaw
open Foundation.Probability NativeUniformSequence

/-- Factor a physical linked execution through a logical result law. The
handoff equality concerns both actual tapes and control, not just output bits. -/
theorem run {Value : Type*} (first second : Program) (T U : ℕ)
    (hFirst : StopsEverywhere first T) (hSecond : StopsEverywhere second U)
    (input output : Tape) (law : PMF Value) (exit entry : Value → Configuration)
    (hLaw : evalConfigWithin first (NativeBitChoice.start input output) T = law.map exit)
    (hEntry : ∀ result, (exit result).resumeAt 0 = entry result) :
    evalConfigWithin (first.followedBy second) (NativeBitChoice.start input output) (T + U + 1) =
      law.bind (fun result => (evalConfigWithin second (entry result) U).map
        (fun c => {c with pc := first.length + second.length + 2, halted := true})) := by
  rw [NativeUniformSequence.run first second T U hFirst hSecond input output, hLaw, PMF.bind_map]
  simp only [Function.comp_def, hEntry]

end Machine.NativeSequenceResultLaw
