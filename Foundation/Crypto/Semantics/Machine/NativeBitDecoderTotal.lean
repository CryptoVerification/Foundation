import Foundation.Crypto.Semantics.Machine.NativeUniformSequence
import Foundation.Crypto.Semantics.Machine.NativePrivateBitResult

/-! Uniform stopping of finite decoders, including early blank input cells. -/
namespace Machine.NativeBitDecoderTotal
open Foundation.Probability NativeBitDecisionTree NativeUniformSequence

theorem stops_mono (p : Program) (input output : Tape) (T U : ℕ) (hTU : T ≤ U)
    (hStop : Stops p input output T) : Stops p input output U := by
  intro finish trace
  have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
  rw [evalConfigWithin_eq_of_le p (NativeBitChoice.start input output) T U hTU hStop] at member
  exact hStop finish ((mem_support_evalConfigWithin_iff _ _ _ _).mp member)

theorem blank_run (zero one : Program) (input output : Tape) (hBlank : input.current = none) :
    evalConfigWithin (NativeBitChoice.code zero one) (NativeBitChoice.start input output) 2 =
      PMF.pure
        ({pc := NativeBitChoice.returnPc zero one, inputTape := input, outputTape := output, halted := true} : Configuration) := by
  have h0 : (NativeBitChoice.code zero one)[0]? = some
      (.branch .input (NativeBitChoice.returnPc zero one) 1 (zero.length + 3)) := rfl
  have hret := NativeBitChoice.code_return_halt zero one
  simp [evalConfigWithin, stepPMF, next, Instruction.next, NativeBitChoice.start,
    Configuration.tape, hBlank, h0, hret]

theorem compile_stops_everywhere (n : ℕ) :
    ∀ (leaves : (Fin n → Bool) → Program) (T : ℕ),
      (∀ bits, StopsEverywhere (leaves bits) T) →
      StopsEverywhere (compile n leaves) (T + 3 * n) := by
  induction n with
  | zero =>
    intro leaves T hLeaves
    simpa only [compile, Nat.mul_zero, Nat.add_zero] using hLeaves (fun i : Fin 0 => Fin.elim0 i)
  | succ n ih =>
    intro leaves T hLeaves input output
    let zero := compile n (fun bits => leaves (Fin.cons false bits))
    let one := compile n (fun bits => leaves (Fin.cons true bits))
    have hz := ih (fun bits => leaves (Fin.cons false bits)) T
      (fun bits => hLeaves (Fin.cons false bits)) input.moveRight output
    have ho := ih (fun bits => leaves (Fin.cons true bits)) T
      (fun bits => hLeaves (Fin.cons true bits)) input.moveRight output
    cases hCell : input.current with
    | none =>
      have hShort : Stops (NativeBitChoice.code zero one) input output 2 := by
        intro finish trace
        have member := (mem_support_evalConfigWithin_iff _ _ _ _).mpr trace
        rw [blank_run zero one input output hCell, PMF.mem_support_pure_iff] at member
        subst finish
        rfl
      exact stops_mono _ input output 2 (T + 3 * (n + 1)) (by omega) hShort
    | some bit =>
      have hTime : (T + 3 * n) + 3 = T + 3 * (n + 1) := by omega
      cases bit with
      | false =>
        have h := NativeBitChoice.halts_zero zero one input output hCell (T + 3 * n) hz
        rw [hTime] at h
        exact h
      | true =>
        have h := NativeBitChoice.halts_one zero one input output hCell (T + 3 * n) ho
        rw [hTime] at h
        exact h

theorem private_payload_stops_everywhere (n : ℕ)
    (payload : (Fin n → Bool) → (Fin 3 → Bool) × Bool) :
    StopsEverywhere (NativePrivateBitResult.compiled n payload) (9 + 3 * n) :=
  compile_stops_everywhere n _ 9 (fun _bits input output =>
    NativePrivateBitResult.stops _ _ input output)

end Machine.NativeBitDecoderTotal
