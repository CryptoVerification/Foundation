import Foundation.Machine.GuardedOutput

namespace Machine

private def segmentInput (bits : List Bool) (tail : List (Option Bool)) : Tape :=
  ({ right := bits.map some ++ none :: tail } : Tape).moveRight

private theorem segmentInput_cons (bit : Bool) (bits : List Bool)
    (tail : List (Option Bool)) :
    segmentInput (bit :: bits) tail =
      { left := [none], current := some bit, right := bits.map some ++ none :: tail } := rfl

private def segmentCopyState (beforeInput beforeOutput tail : List (Option Bool))
    (copied remaining : List Bool) (blanks : Nat) : Configuration :=
  { inputTape := { segmentInput remaining tail with
      left := copied.reverse.map some ++ beforeInput },
    outputTape := {
      left := copied.reverse.map some ++ beforeOutput
      right := List.replicate blanks none } }

def copySegmentStart (beforeInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) : Configuration :=
  segmentCopyState beforeInput beforeOutput tail [] bits blanks

theorem copySegmentStart_layout (beforeInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    copySegmentStart beforeInput beforeOutput tail bits blanks =
      ({
        inputTape := { ({ right := bits.map some ++ none :: tail } : Tape).moveRight with
          left := beforeInput }
        outputTape := { left := beforeOutput, right := List.replicate blanks none } } : Configuration) := by
  simp [copySegmentStart, segmentCopyState, segmentInput]

def copySegmentFinish (beforeInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) : Configuration :=
  { pc := 7,
    inputTape := { left := bits.reverse.map some ++ beforeInput, right := tail },
    outputTape := {
      left := bits.reverse.map some ++ beforeOutput
      right := List.replicate (blanks - bits.length) none },
    halted := true }

private theorem copy_segment_bit (beforeInput beforeOutput tail : List (Option Bool))
    (copied rest : List Bool) (bit : Bool) (blanks : Nat) :
    RunsFor copyBitstring (segmentCopyState beforeInput beforeOutput tail copied (bit :: rest) blanks)
      (segmentCopyState beforeInput beforeOutput tail (copied ++ [bit]) rest (blanks - 1))
      (if bit then 5 else 6) := by
  let initial := segmentCopyState beforeInput beforeOutput tail copied (bit :: rest) blanks
  let selected : Configuration := { initial with pc := if bit then 3 else 1 }
  let written : Configuration := { initial with
    pc := if bit then 4 else 2
    outputTape := initial.outputTape.write (some bit) }
  let ready : Configuration := { written with pc := 4 }
  let movedInput : Configuration := { ready with pc := 5, inputTape := ready.inputTape.moveRight }
  let movedOutput : Configuration := { movedInput with pc := 6, outputTape := movedInput.outputTape.moveRight }
  have h0 : Step copyBitstring initial selected := by
    cases bit <;> simp [Step, successors, next, copyBitstring, initial, selected,
      segmentCopyState, segmentInput_cons, Instruction.next, Configuration.tape]
  have h1 : Step copyBitstring selected written := by
    cases bit <;> simp [Step, successors, next, copyBitstring, initial, selected, written,
      segmentCopyState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h2 : Step copyBitstring ready movedInput := by
    simp [Step, successors, next, copyBitstring, initial, written, ready, movedInput,
      segmentCopyState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h3 : Step copyBitstring movedInput movedOutput := by
    simp [Step, successors, next, copyBitstring, initial, written, ready, movedInput, movedOutput,
      segmentCopyState, Instruction.next, Configuration.updateTape, Configuration.advance]
  have h4 : Step copyBitstring movedOutput
      (segmentCopyState beforeInput beforeOutput tail (copied ++ [bit]) rest (blanks - 1)) := by
    cases blanks <;> cases rest <;>
      simp [Step, successors, next, copyBitstring, initial, written, ready, movedInput,
        movedOutput, segmentCopyState, segmentInput, Instruction.next,
        Tape.moveRight, Tape.write, List.reverse_append, List.replicate_succ]
  cases bit with
  | false =>
      have hJump : Step copyBitstring written ready := by
        simp [Step, successors, next, copyBitstring, initial, written, ready,
          segmentCopyState, Instruction.next]
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1) hJump) h2) h3) h4
  | true =>
      have hReady : ready = written := by simp [ready, written]
      rw [hReady] at h2
      exact RunsFor.succ (RunsFor.succ (RunsFor.succ (RunsFor.succ
        (RunsFor.succ (RunsFor.zero _) h0) h1) h2) h3) h4

private theorem copy_segment_loop (beforeInput beforeOutput tail : List (Option Bool))
    (copied remaining : List Bool) (blanks : Nat) :
    RunsFor copyBitstring (segmentCopyState beforeInput beforeOutput tail copied remaining blanks)
      (copySegmentFinish beforeInput beforeOutput tail (copied ++ remaining) (blanks + copied.length))
      (copyBitstringSteps remaining) := by
  induction remaining generalizing copied blanks with
  | nil =>
      let initial := segmentCopyState beforeInput beforeOutput tail copied [] blanks
      let selected : Configuration := { initial with pc := 7 }
      have h0 : Step copyBitstring initial selected := by
        simp [Step, successors, next, copyBitstring, initial, selected, segmentCopyState,
          segmentInput, Tape.moveRight, Instruction.next, Configuration.tape]
      have h1 : Step copyBitstring selected
          (copySegmentFinish beforeInput beforeOutput tail copied (blanks + copied.length)) := by
        simp [Step, successors, next, copyBitstring, initial, selected, segmentCopyState,
          segmentInput, Tape.moveRight, copySegmentFinish, Instruction.next]
      simpa [copyBitstringSteps] using RunsFor.succ (RunsFor.succ (RunsFor.zero _) h0) h1
  | cons bit rest ih =>
      have run := (copy_segment_bit beforeInput beforeOutput tail copied rest bit blanks).trans
        (ih (copied ++ [bit]) (blanks - 1))
      have hFinish : copySegmentFinish beforeInput beforeOutput tail ((copied ++ [bit]) ++ rest)
          (blanks - 1 + (copied ++ [bit]).length) =
          copySegmentFinish beforeInput beforeOutput tail (copied ++ bit :: rest) (blanks + copied.length) := by
        have hSubtract : blanks - 1 + (copied ++ [bit]).length - (copied ++ bit :: rest).length =
            blanks + copied.length - (copied ++ bit :: rest).length := by simp; omega
        simp only [copySegmentFinish, List.append_assoc, List.singleton_append]
        rw [hSubtract]
      rw [hFinish] at run
      exact run

/-- Copy exactly the bit segment ending at the next blank. The cells after
that blank may contain arbitrary caller data, and remain unchanged. Both
saved prefixes and explicit output blank padding are retained. -/
theorem copySegment_runs (beforeInput beforeOutput tail : List (Option Bool))
    (bits : List Bool) (blanks : Nat) :
    RunsFor copyBitstring (copySegmentStart beforeInput beforeOutput tail bits blanks)
      (copySegmentFinish beforeInput beforeOutput tail bits blanks) (copyBitstringSteps bits) := by
  simpa [copySegmentStart] using copy_segment_loop beforeInput beforeOutput tail [] bits blanks


end Machine
