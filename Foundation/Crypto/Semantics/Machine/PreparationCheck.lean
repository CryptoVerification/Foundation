import Foundation.Crypto.Semantics.Machine.PreparationFailure
import Foundation.Crypto.Semantics.ProcedureSimulation

/-! Unequal physical operands are rejected with restored input heads and an
actual tagged response tape. The successful branch retains the ready buffer
for a subsequent native component. -/
namespace Machine.PreparationCheck
open Foundation.Probability TimedExecution

inductive Control where
  | preparing (preparation : PairPreparation.Control)
  | failure (recovery : PreparationFailure.Control)
  deriving DecidableEq

noncomputable def step : Control → PMF Control
  | .preparing (.rejected first second buffer) =>
      PMF.pure (.failure (.detected first second buffer))
  | .preparing preparation => (PairPreparation.step preparation).map .preparing
  | .failure recovery => (PreparationFailure.step recovery).map .failure

def boundary : PairPreparation.Control → Bool
  | .ready _ _ _ | .rejected _ _ _ => true
  | _ => false

def targetBoundary : Control → Bool
  | .preparing preparation => boundary preparation
  | .failure _ => true

structure FailureInput where
  first : List Bool
  second : List Bool
  firstTail : List (Option Bool)
  secondTail : List (Option Bool)
  mismatch : first.length ≠ second.length

def consumed (input : FailureInput) := min input.first.length input.second.length

def tapes (input : FailureInput) : Tape × Tape × Tape :=
  (PairPreparation.operand (input.first.take (consumed input))
      (input.first.drop (consumed input)) input.firstTail,
   PairPreparation.operand (input.second.take (consumed input))
      (input.second.drop (consumed input)) input.secondTail,
   { left := (PairPreparation.interleave input.first input.second).reverse.map some })

noncomputable def scan (input : FailureInput) : TimedExecution.Procedure step Unit Unit :=
  (TimedExecution.Procedure.ofFixed PairPreparation.step
    (fun _ : Unit => .reading (PairPreparation.operand [] input.first input.firstTail)
      (PairPreparation.operand [] input.second input.secondTail) {})
    (fun _ _ => .rejected (tapes input).1 (tapes input).2.1 (tapes input).2.2)
    (fun _ => PMF.pure ()) (fun _ => 8 * consumed input + 2)
    (fun _ => by simpa [tapes, consumed, PMF.pure_map] using
      PairPreparation.reject [] [] input.first input.second input.firstTail input.secondTail [] input.mismatch)).liftBoundary
    boundary (fun _ _ _ => rfl)
    (fun preparation h => by cases preparation <;> simp_all [boundary, PairPreparation.step])
    (fun _ _ => ()) (fun _ _ => rfl)
    step targetBoundary Control.preparing (fun _ => rfl)
    (fun preparation h => by cases preparation <;> simp_all [boundary, step])

noncomputable def handoff (input : FailureInput) : TimedExecution.Procedure step Unit Unit :=
  TimedExecution.Procedure.ofFixed step
    (fun _ => .preparing (.rejected (tapes input).1 (tapes input).2.1 (tapes input).2.2))
    (fun _ _ => .failure (.detected (tapes input).1 (tapes input).2.1 (tapes input).2.2))
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun _ => by simp [eval, step, PMF.pure_map])

noncomputable def recovery (input : FailureInput) :=
  ((PreparationFailure.procedure.transport step Control.failure (fun _ => rfl)).reindex
    (fun _ : Unit => tapes input))

noncomputable def complete (input : FailureInput) :=
  ((scan input).seq (handoff input) (fun _ _ _ => rfl) (fun _ => 1)
    (fun _ _ _ => Nat.le_refl _)).seq
    ((recovery input).reindex (fun _ => ())) (fun _ _ _ => rfl)
    (fun _ => (recovery input).budget ()) (fun _ _ _ => Nat.le_refl _)

theorem budget (input : FailureInput) :
    (complete input).budget () = 12 * consumed input + 10 := by
  simp [complete, scan, handoff, recovery, TimedExecution.Procedure.seq,
    TimedExecution.Procedure.liftBoundary, TimedExecution.Procedure.ofFixed,
    TimedExecution.Procedure.transport, TimedExecution.Procedure.reindex,
    PreparationFailure.procedure, tapes, PairPreparation.operand,
    PairPreparation.interleave_length_min, List.length_take, consumed]
  omega

theorem restored_operand (past remaining : List Bool) (tail : List (Option Bool)) :
    PreparationFailure.restored (PairPreparation.operand past remaining tail) =
      PairPreparation.operand [] (past ++ remaining) tail := by
  cases remaining <;> simp [PreparationFailure.restored, PairPreparation.operand,
    PairPreparation.fromCells, List.map_reverse, List.map_append, List.append_assoc]

def final (input : FailureInput) : Control :=
  .failure (.returned (PairPreparation.operand [] input.first input.firstTail)
    (PairPreparation.operand [] input.second input.secondTail) (ResponseExport.endTape [false]))

theorem run (input : FailureInput) :
    eval step (12 * consumed input + 10)
      (.preparing (.reading (PairPreparation.operand [] input.first input.firstTail)
        (PairPreparation.operand [] input.second input.secondTail) {})) = PMF.pure (final input) := by
  have h := (complete input).final_run () (fun _ _ => by
    simp [complete, recovery, TimedExecution.Procedure.seq, TimedExecution.Procedure.reindex,
      TimedExecution.Procedure.transport, PreparationFailure.procedure,
      TimedExecution.Procedure.ofFixed, step, PreparationFailure.step, PMF.pure_map])
    (12 * consumed input + 10) (by rw [budget])
  simpa [complete, scan, handoff, recovery, TimedExecution.Procedure.seq,
    TimedExecution.Procedure.liftBoundary, TimedExecution.Procedure.ofFixed,
    TimedExecution.Procedure.transport, TimedExecution.Procedure.reindex,
    PreparationFailure.procedure, tapes, restored_operand, final, List.take_append_drop, PMF.pure_map] using h

noncomputable def success : TimedExecution.Procedure step PairPreparation.Input Unit :=
  PairPreparation.procedure.liftBoundary boundary (fun _ _ _ => rfl)
    (fun preparation h => by cases preparation <;> simp_all [boundary, PairPreparation.step])
    (fun _ _ => ()) (fun _ _ => rfl)
    step targetBoundary Control.preparing (fun _ => rfl)
    (fun preparation h => by cases preparation <;> simp_all [boundary, step])

theorem success_run (input : PairPreparation.Input) :
    eval step (12 * input.first.length + 3)
      (.preparing (.reading (PairPreparation.operand [] input.first input.firstTail)
        (PairPreparation.operand [] input.second input.secondTail) {})) =
      PMF.pure (.preparing (.ready (PairPreparation.operand [] input.first input.firstTail)
        (PairPreparation.operand [] input.second input.secondTail)
        (PairPreparation.fromCells ((PairPreparation.interleave input.first input.second).map some ++ [none])))) := by
  have h := success.final_run input (fun _ _ => by
    simp [success, TimedExecution.Procedure.liftBoundary, PairPreparation.procedure,
      TimedExecution.Procedure.ofFixed, step, PairPreparation.step, PMF.pure_map])
    (12 * input.first.length + 3) (Nat.le_refl _)
  simpa [success, TimedExecution.Procedure.liftBoundary, PairPreparation.procedure,
    TimedExecution.Procedure.ofFixed, PMF.pure_map] using h

end Machine.PreparationCheck
