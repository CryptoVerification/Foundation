import Foundation.Crypto.Semantics.Machine.Procedure
import Foundation.Crypto.Semantics.Machine.TapeEquivalence

/-! A finite controller prepares alternating operands from two physical
tapes. Each read, write and head move is charged. Both source heads and the
buffer head are restored; unequal lengths produce an explicit rejection. -/
namespace Machine.PairPreparation
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

inductive Control where
  | reading (first second buffer : Tape)
  | checking (bit : Bool) (first second buffer : Tape)
  | writingFirst (bit next : Bool) (first second buffer : Tape)
  | advancingFirst (next : Bool) (first second buffer : Tape)
  | writingSecond (bit : Bool) (first second buffer : Tape)
  | advancingSecond (first second buffer : Tape)
  | advancingKey (first second buffer : Tape)
  | advancingMessage (first second buffer : Tape)
  | checkingEnd (first second buffer : Tape)
  | rewinding (first second buffer : Tape)
  | ready (first second buffer : Tape)
  | rejected (first second buffer : Tape)
  deriving DecidableEq

noncomputable def step : Control → PMF Control
  | .reading first second buffer =>
      match first.current with
      | none => PMF.pure (.checkingEnd first second buffer)
      | some bit => PMF.pure (.checking bit first second buffer)
  | .checking bit first second buffer =>
      match second.current with
      | none => PMF.pure (.rejected first second buffer)
      | some next => PMF.pure (.writingFirst bit next first second buffer)
  | .writingFirst bit next first second buffer =>
      PMF.pure (.advancingFirst next first second (buffer.write (some bit)))
  | .advancingFirst next first second buffer =>
      PMF.pure (.writingSecond next first second buffer.moveRight)
  | .writingSecond bit first second buffer =>
      PMF.pure (.advancingSecond first second (buffer.write (some bit)))
  | .advancingSecond first second buffer =>
      PMF.pure (.advancingKey first second buffer.moveRight)
  | .advancingKey first second buffer =>
      PMF.pure (.advancingMessage first.moveRight second buffer)
  | .advancingMessage first second buffer =>
      PMF.pure (.reading first second.moveRight buffer)
  | .checkingEnd first second buffer =>
      match second.current with
      | none => PMF.pure (.rewinding first second buffer)
      | some _ => PMF.pure (.rejected first second buffer)
  | .rewinding first second buffer =>
      match first.left with
      | _ :: _ => PMF.pure (.rewinding first.moveLeft second buffer)
      | [] => match second.left with
        | _ :: _ => PMF.pure (.rewinding first second.moveLeft buffer)
        | [] => match buffer.left with
          | _ :: _ => PMF.pure (.rewinding first second buffer.moveLeft)
          | [] => PMF.pure (.ready first second buffer)
  | .ready first second buffer => PMF.pure (.ready first second buffer)
  | .rejected first second buffer => PMF.pure (.rejected first second buffer)

def fromCells (cells : List (Option Bool)) : Tape := ⟨[], cells.headD none, cells.tail⟩

def operand (past remaining : List Bool) (tail : List (Option Bool)) : Tape :=
  { (fromCells (remaining.map some ++ none :: tail)) with left := past.reverse.map some }

def interleave : List Bool → List Bool → List Bool
  | first :: rest, second :: more => first :: second :: interleave rest more
  | _, _ => []

theorem interleave_length (first second : List Bool) (h : first.length = second.length) :
    (interleave first second).length = 2 * first.length := by
  induction first generalizing second with
  | nil => simp [interleave]
  | cons bit first ih =>
      cases second with
      | nil => simp at h
      | cons next second => simp only [List.length_cons] at h; simp [interleave, ih second (by omega)]; omega

theorem interleave_length_min (first second : List Bool) :
    (interleave first second).length = 2 * min first.length second.length := by
  induction first generalizing second with
  | nil => simp [interleave]
  | cons bit first ih =>
      cases second with
      | nil => simp [interleave]
      | cons next second => simp [interleave, ih]; omega

theorem iteration (pastFirst pastSecond first second : List Bool) (bit next : Bool)
    (firstTail secondTail before : List (Option Bool)) :
    eval step 8 (.reading (operand pastFirst (bit :: first) firstTail)
      (operand pastSecond (next :: second) secondTail) { left := before }) =
      PMF.pure (.reading (operand (pastFirst ++ [bit]) first firstTail)
        (operand (pastSecond ++ [next]) second secondTail) { left := some next :: some bit :: before }) := by
  cases first <;> cases second <;>
    simp [eval, step, operand, fromCells, Tape.write, Tape.moveRight,
      List.reverse_append]

theorem scan (pastFirst pastSecond first second : List Bool)
    (firstTail secondTail before : List (Option Bool)) (h : first.length = second.length) :
    eval step (8 * first.length + 2)
      (.reading (operand pastFirst first firstTail) (operand pastSecond second secondTail) { left := before }) =
      PMF.pure (.rewinding (operand (pastFirst ++ first) [] firstTail)
        (operand (pastSecond ++ second) [] secondTail)
        { left := (interleave first second).reverse.map some ++ before }) := by
  induction first generalizing second pastFirst pastSecond before with
  | nil =>
      have hs : second = [] := List.length_eq_zero_iff.mp (by simpa using h.symm)
      subst second
      simp [eval, step, operand, fromCells, interleave]
  | cons bit first ih =>
      cases second with
      | nil => simp at h
      | cons next second =>
          have hl : first.length = second.length := by simpa using h
          rw [show 8 * (bit :: first).length + 2 = 8 + (8 * first.length + 2) by simp; omega,
            eval_add, iteration, PMF.pure_bind, ih _ _ _ _ hl]
          simp [interleave, List.reverse_cons, List.map_append, List.append_assoc]

theorem rewind (firstLeft secondLeft bufferLeft : List (Option Bool))
    (firstCurrent secondCurrent bufferCurrent : Option Bool)
    (firstRight secondRight bufferRight : List (Option Bool)) :
    eval step (firstLeft.length + secondLeft.length + bufferLeft.length + 1)
      (.rewinding ⟨firstLeft, firstCurrent, firstRight⟩
        ⟨secondLeft, secondCurrent, secondRight⟩ ⟨bufferLeft, bufferCurrent, bufferRight⟩) =
      PMF.pure (.ready (fromCells (firstLeft.reverse ++ firstCurrent :: firstRight))
        (fromCells (secondLeft.reverse ++ secondCurrent :: secondRight))
        (fromCells (bufferLeft.reverse ++ bufferCurrent :: bufferRight))) := by
  induction firstLeft generalizing firstCurrent firstRight with
  | cons cell firstLeft ih =>
      rw [show (cell :: firstLeft).length + secondLeft.length + bufferLeft.length + 1 =
        (firstLeft.length + secondLeft.length + bufferLeft.length + 1) + 1 by simp; omega, eval]
      simp only [step, Tape.moveLeft, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]
  | nil =>
      induction secondLeft generalizing secondCurrent secondRight with
      | cons cell secondLeft ih =>
          rw [show ([] : List (Option Bool)).length + (cell :: secondLeft).length + bufferLeft.length + 1 =
            (([] : List (Option Bool)).length + secondLeft.length + bufferLeft.length + 1) + 1 by simp; omega, eval]
          simp only [step, Tape.moveLeft, PMF.pure_bind]
          rw [ih]
          simp [List.reverse_cons, List.append_assoc]
      | nil =>
          induction bufferLeft generalizing bufferCurrent bufferRight with
          | nil => simp [eval, step, fromCells]
          | cons cell bufferLeft ih =>
              rw [show ([] : List (Option Bool)).length + ([] : List (Option Bool)).length +
                (cell :: bufferLeft).length + 1 =
                (([] : List (Option Bool)).length + ([] : List (Option Bool)).length + bufferLeft.length + 1) + 1 by simp,
                eval]
              simp only [step, Tape.moveLeft, PMF.pure_bind]
              rw [ih]
              simp [List.reverse_cons, List.append_assoc]

theorem run (first second : List Bool) (firstTail secondTail : List (Option Bool))
    (h : first.length = second.length) :
    eval step (12 * first.length + 3)
      (.reading (operand [] first firstTail) (operand [] second secondTail) {}) =
      PMF.pure (.ready (operand [] first firstTail) (operand [] second secondTail)
        (fromCells ((interleave first second).map some ++ [none]))) := by
  have hLen := interleave_length first second h
  rw [show 12 * first.length + 3 = (8 * first.length + 2) +
    (first.reverse.length + second.reverse.length + (interleave first second).reverse.length + 1) by simp; omega,
    eval_add, scan [] [] first second firstTail secondTail [] h, PMF.pure_bind]
  simp only [operand, fromCells, List.map_nil, List.nil_append, List.append_nil,
    List.headD_cons, List.tail_cons]
  rw [show first.reverse.length + second.reverse.length + (interleave first second).reverse.length + 1 =
    (first.reverse.map some).length + (second.reverse.map some).length +
      ((interleave first second).reverse.map some).length + 1 by simp, rewind]
  simp [fromCells, List.map_reverse]

theorem reject (pastFirst pastSecond first second : List Bool)
    (firstTail secondTail before : List (Option Bool)) (h : first.length ≠ second.length) :
    eval step (8 * min first.length second.length + 2)
      (.reading (operand pastFirst first firstTail) (operand pastSecond second secondTail) { left := before }) =
      PMF.pure (.rejected
        (operand (pastFirst ++ first.take (min first.length second.length))
          (first.drop (min first.length second.length)) firstTail)
        (operand (pastSecond ++ second.take (min first.length second.length))
          (second.drop (min first.length second.length)) secondTail)
        { left := (interleave first second).reverse.map some ++ before }) := by
  induction first generalizing second pastFirst pastSecond before with
  | nil =>
      cases second with
      | nil => contradiction
      | cons bit second => simp [eval, step, operand, fromCells, interleave]
  | cons bit first ih =>
      cases second with
      | nil => simp [eval, step, operand, fromCells, interleave]
      | cons next second =>
          have hl : first.length ≠ second.length := by simpa using h
          rw [show 8 * min (bit :: first).length (next :: second).length + 2 =
            8 + (8 * min first.length second.length + 2) by simp; omega,
            eval_add, iteration, PMF.pure_bind]
          rw [ih _ _ _ _ hl]
          simp [interleave, List.reverse_cons, List.map_append, List.append_assoc]

private theorem getD_append_blank (cells : List (Option Bool)) (i : Nat) :
    (cells ++ [none]).getD i none = cells.getD i none := by
  induction cells generalizing i with
  | nil => cases i <;> simp
  | cons cell cells ih => cases i with
    | zero => rfl
    | succ i => exact ih i

/-- This is a cell-equivalence proof, not an uncharged normalization step. -/
theorem prepared_equivalent (bits : List Bool) :
    (fromCells (bits.map some ++ [none])).Equivalent (Tape.ofBits bits) := by
  cases bits with
  | nil => exact Tape.Equivalent.refl _
  | cons bit bits => exact ⟨rfl, fun _ => rfl, getD_append_blank (bits.map some)⟩

structure Input where
  first : List Bool
  second : List Bool
  firstTail : List (Option Bool)
  secondTail : List (Option Bool)
  sameLength : first.length = second.length

/-- The logical operands describe the existing physical source tapes. -/
noncomputable def procedure : TimedExecution.Procedure step Input Unit :=
  TimedExecution.Procedure.ofFixed step
    (fun input => .reading (operand [] input.first input.firstTail) (operand [] input.second input.secondTail) {})
    (fun input _ => .ready (operand [] input.first input.firstTail) (operand [] input.second input.secondTail)
      (fromCells ((interleave input.first input.second).map some ++ [none])))
    (fun _ => PMF.pure ()) (fun input => 12 * input.first.length + 3)
    (fun input => by simpa only [PMF.pure_map] using
      PairPreparation.run input.first input.second input.firstTail input.secondTail input.sameLength)

end Machine.PairPreparation
