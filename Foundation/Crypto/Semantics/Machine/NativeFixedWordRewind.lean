import Foundation.Crypto.Semantics.Machine.NativeBoundedFlaggedTransfer

/-! Fixed-count head rewinding with arbitrary retained tape frames.
The opposite-tape program is statically relabeled native syntax. -/
namespace Machine.NativeFixedWordRewind
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence NativeBoundedFlaggedTransfer

theorem stops_swap (p : Program) (T : ℕ) (hStop : StopsEverywhere p T) :
    StopsEverywhere p.swapTapes T := by
  intro input output finish trace
  have h := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  change finish ∈ (evalConfigWithin p.swapTapes (NativeBitChoice.start output input).swapTapes T).support at h
  rw [evalConfigWithin_swapTapes, PMF.mem_support_map_iff] at h
  obtain ⟨source, hSource, rfl⟩ := h
  exact hStop output input source ((mem_support_evalConfigWithin_iff _ _ _ _).mp hSource)

theorem left_actions (bits : List Bool) (suffix : Tape) :
    NativePrivateHistoryErasure.applyActions (List.replicate bits.length .left) (afterRead bits suffix) =
      preload bits suffix := by
  induction bits using List.reverseRecOn generalizing suffix with
  | nil => rfl
  | append_singleton bits bit ih =>
    have hm : (afterRead (bits ++ [bit]) suffix).moveLeft = afterRead bits (consBit bit suffix) := by
      simp [afterRead, consBit, List.reverse_append, Tape.moveLeft]
    simp only [List.length_append, List.length_singleton, List.replicate_succ,
      NativePrivateHistoryErasure.applyActions, NativePrivateHistoryErasure.act]
    rw [hm, ih]
    exact (preload_append bits [bit] suffix).symm

def inputCode (n : ℕ) : Program := NativePrivateHistoryErasure.code (List.replicate n .left)

def outputCode (n : ℕ) : Program := (inputCode n).swapTapes

theorem input_stops (n : ℕ) : StopsEverywhere (inputCode n) (3 * n + 1) := by
  simpa only [inputCode, List.length_replicate] using NativePrivateHistoryErasure.stops (List.replicate n .left)

theorem output_stops (n : ℕ) : StopsEverywhere (outputCode n) (3 * n + 1) :=
  stops_swap _ _ (input_stops n)

theorem output_length (n : ℕ) : (outputCode n).length = 5 * n + 1 := by
  unfold outputCode inputCode
  rw [Program.swapTapes_length, NativePrivateHistoryErasure.code_length, List.length_replicate]

theorem output_run (bits : List Bool) (suffix other : Tape) :
    evalConfigWithin (outputCode bits.length) (NativeBitChoice.start other (afterRead bits suffix))
      (3 * bits.length + 1) =
      PMF.pure {pc := 5 * bits.length, inputTape := other, outputTape := preload bits suffix, halted := true} := by
  unfold outputCode inputCode
  change evalConfigWithin (NativePrivateHistoryErasure.code (List.replicate bits.length .left)).swapTapes
    (NativeBitChoice.start (afterRead bits suffix) other).swapTapes _ = _
  rw [evalConfigWithin_swapTapes]
  have h := NativePrivateHistoryErasure.run (List.replicate bits.length .left) (afterRead bits suffix) other
  simp only [List.length_replicate, left_actions, NativePrivateHistoryErasure.code_length] at h
  rw [h, PMF.pure_map]
  simp only [Nat.add_sub_cancel]
  rfl

end Machine.NativeFixedWordRewind
