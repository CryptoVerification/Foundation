import Foundation.Crypto.Semantics.Machine.ResponseExport
import Foundation.Crypto.Semantics.ProcedureSimulation

/-! A generic native sampler transfers its actual output to a private store.
Each head move and ownership transfer is charged; runtime never evaluates
an encoder to manufacture a sampled key. -/
namespace Machine.PrivateInitialization
open Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false

inductive Control where
  | generating (machine : Configuration)
  | rewinding (tape : Tape)
  | ready (tape : Tape)
  deriving DecidableEq

noncomputable def step (code : Program) : Control → PMF Control
  | .generating machine =>
      if machine.halted then PMF.pure (.rewinding machine.outputTape)
      else (stepPMF code machine).map .generating
  | .rewinding tape =>
      match tape.left with
      | [] => PMF.pure (.ready tape)
      | _ :: _ => PMF.pure (.rewinding tape.moveLeft)
  | .ready tape => PMF.pure (.ready tape)

def boundary : Control → Bool
  | .generating machine => machine.halted
  | _ => true

theorem rewind (code : Program) (left : List (Option Bool)) (current : Option Bool)
    (right : List (Option Bool)) :
    TimedExecution.eval (step code) (left.length + 1) (.rewinding ⟨left, current, right⟩) =
      PMF.pure (.ready (ResponseExport.fromCells (left.reverse ++ current :: right))) := by
  induction left generalizing current right with
  | nil => simp [TimedExecution.eval, step, ResponseExport.fromCells]
  | cons cell left ih =>
      rw [show (cell :: left).length + 1 = (left.length + 1) + 1 by rfl, TimedExecution.eval]
      simp only [step, Tape.moveLeft, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

variable {Input : Type u} {Output : Type v}
    (P : Machine.Procedure Input Output) (encode : Output → List Bool)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (hTape : ∀ input output, (P.execution.exit input output).outputTape = ResponseExport.endTape (encode output))
    (read : Input → Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (cap : Input → Nat)
    (hCap : ∀ input output, output ∈ (P.execution.semantics input).support → (encode output).length ≤ cap input)

noncomputable def generating :=
  P.execution.liftBoundary Configuration.halted (fun input output _ => hHalt input output)
    (fun machine h => by simp [stepPMF, next, h]) read hRead
    (step P.code) boundary Control.generating (fun _ => rfl)
    (fun machine h => by simp [step, h])

noncomputable def transfer : TimedExecution.Procedure (step P.code) (Input × Output) Unit :=
  TimedExecution.Procedure.ofFixed _
    (fun input => .generating (P.execution.exit input.1 input.2))
    (fun input _ => .rewinding (ResponseExport.endTape (encode input.2)))
    (fun _ => PMF.pure ()) (fun _ => 1)
    (fun input => by simp [TimedExecution.eval, step, hHalt, hTape, PMF.pure_map])

noncomputable def restoring : TimedExecution.Procedure (step P.code) ((Input × Output) × Unit) Unit :=
  TimedExecution.Procedure.ofFixed _
    (fun input => .rewinding (ResponseExport.endTape (encode input.1.2)))
    (fun input _ => .ready (ResponseExport.fromCells ((encode input.1.2).map some ++ [none])))
    (fun _ => PMF.pure ()) (fun input => (encode input.1.2).length + 1)
    (fun input => by
      simpa [ResponseExport.endTape, List.map_reverse, PMF.pure_map] using
        rewind P.code ((encode input.1.2).reverse.map some) none [])

noncomputable def procedure :=
  ((generating P hHalt read hRead).remember.seq
    (transfer P encode hHalt hTape) (fun _ _ _ => rfl) (fun _ => 1) (fun _ _ _ => Nat.le_refl _)).seq
    (restoring P encode) (fun _ _ _ => rfl) (fun input => cap input + 1)
    (fun input result hResult => by
      simp only [Procedure.seq, Procedure.remember, generating, Procedure.liftBoundary,
        transfer, TimedExecution.Procedure.ofFixed, PMF.mem_support_bind_iff] at hResult
      obtain ⟨middle, hMiddle, hResult⟩ := hResult
      rw [PMF.mem_support_map_iff] at hMiddle
      obtain ⟨output, hOutput, he⟩ := hMiddle
      subst middle
      simp only [PMF.pure_map, PMF.mem_support_pure_iff] at hResult
      subst result
      change (encode output).length + 1 ≤ cap input + 1
      exact Nat.add_le_add_right (hCap input output hOutput) 1)

theorem budget (input : Input) :
    (procedure P encode hHalt hTape read hRead cap hCap).budget input = P.execution.budget input + cap input + 2 := by
  change P.execution.budget input + 1 + (cap input + 1) = _
  omega

theorem semantics (input : Input) :
    (procedure P encode hHalt hTape read hRead cap hCap).semantics input =
      (P.execution.semantics input).map (fun output => (((input, output), ()), ())) := by
  simp [procedure, generating, transfer, restoring, Procedure.seq, Procedure.remember,
    Procedure.liftBoundary, TimedExecution.Procedure.ofFixed, PMF.map, PMF.bind_bind, Function.comp_def]

theorem distribution (input : Input) :
    ((procedure P encode hHalt hTape read hRead cap hCap).costed input).map
      (fun result => (procedure P encode hHalt hTape read hRead cap hCap).exit input result.1) =
      (P.execution.semantics input).map (fun output =>
        Control.ready (ResponseExport.fromCells ((encode output).map some ++ [none]))) := by
  have h := congrArg (fun distribution => distribution.map
    ((procedure P encode hHalt hTape read hRead cap hCap).exit input))
    ((procedure P encode hHalt hTape read hRead cap hCap).correct input)
  rw [semantics] at h
  simp only [PMF.map_comp, Function.comp_def] at h
  exact h
/-- A logical view of the sampled key, with the same physical endpoint.
The ready state is absorbing only inside this initialization component. -/
noncomputable def sample : TimedExecution.Procedure (step P.code) Input Output :=
  TimedExecution.Procedure.ofFixed _
    (fun input => .generating (P.execution.entry input))
    (fun _ output => .ready (ResponseExport.fromCells ((encode output).map some ++ [none])))
    P.execution.semantics (fun input => P.execution.budget input + cap input + 2)
    (fun input => by
      have h := (procedure P encode hHalt hTape read hRead cap hCap).final_run input
        (fun _ _ => by simp [procedure, restoring, Procedure.seq, TimedExecution.Procedure.ofFixed, step])
        (P.execution.budget input + cap input + 2) (by rw [budget])
      rw [semantics] at h
      simpa only [PMF.map_comp, Function.comp_def, procedure, generating, transfer, restoring,
        Procedure.seq, Procedure.remember, Procedure.liftBoundary, TimedExecution.Procedure.ofFixed] using h)

end Machine.PrivateInitialization
