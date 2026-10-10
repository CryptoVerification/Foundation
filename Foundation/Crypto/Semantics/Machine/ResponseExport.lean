import Foundation.Crypto.Semantics.Machine.Procedure
import Foundation.Crypto.Semantics.ProcedureBoundary
import Foundation.Crypto.Semantics.Framing

/-! Export a halted native component's physical output, one cell per step.
The finite controller rewinds, scans to the first blank, and reverses the
collected packet. It never evaluates a semantic encoder at runtime. -/
namespace Machine.ResponseExport
open Foundation.Probability TimedExecution
universe u v
set_option backward.isDefEq.respectTransparency false

inductive Control where
  | running (machine : Configuration)
  | rewinding (tape : Tape)
  | collecting (tape : Tape) (reversed : List Bool)
  | reversing (remaining packet : List Bool)
  | returned (packet : List Bool)
  deriving DecidableEq

noncomputable def step (code : Program) : Control → PMF Control
  | .running machine =>
      if machine.halted then PMF.pure (.rewinding machine.outputTape)
      else (stepPMF code machine).map .running
  | .rewinding tape =>
      match tape.left with
      | [] => PMF.pure (.collecting tape [])
      | _ :: _ => PMF.pure (.rewinding tape.moveLeft)
  | .collecting tape reversed =>
      match tape.current with
      | none => PMF.pure (.reversing reversed [])
      | some bit => PMF.pure (.collecting tape.moveRight (bit :: reversed))
  | .reversing remaining packet =>
      match remaining with
      | [] => PMF.pure (.returned packet)
      | bit :: rest => PMF.pure (.reversing rest (bit :: packet))
  | .returned packet => PMF.pure (.returned packet)

def boundary : Control → Bool
  | .running machine => machine.halted
  | _ => true

def fromCells (cells : List (Option Bool)) : Tape := ⟨[], cells.headD none, cells.tail⟩

def endTape (packet : List Bool) : Tape := ⟨packet.reverse.map some, none, []⟩

theorem rewind (code : Program) (left : List (Option Bool)) (current : Option Bool)
    (right : List (Option Bool)) :
    eval (step code) (left.length + 1) (.rewinding ⟨left, current, right⟩) =
      PMF.pure (.collecting (fromCells (left.reverse ++ current :: right)) []) := by
  induction left generalizing current right with
  | nil => simp [eval, step, fromCells]
  | cons cell left ih =>
      rw [show (cell :: left).length + 1 = (left.length + 1) + 1 by rfl, eval]
      simp only [step, Tape.moveLeft, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem collect (code : Program) (packet reversed : List Bool) (tail before : List (Option Bool)) :
    eval (step code) (packet.length + 1)
      (.collecting { (fromCells (packet.map some ++ none :: tail)) with left := before } reversed) =
      PMF.pure (.reversing (packet.reverse ++ reversed) []) := by
  induction packet generalizing reversed before with
  | nil => simp [eval, step, fromCells]
  | cons bit packet ih =>
      rw [show (bit :: packet).length + 1 = (packet.length + 1) + 1 by rfl, eval]
      simp only [step, fromCells, List.map_cons, List.cons_append, List.headD_cons,
        List.tail_cons, Tape.moveRight, PMF.pure_bind]
      have ht := ih (bit :: reversed) (some bit :: before)
      cases packet with
      | nil => simpa [fromCells] using ht
      | cons next rest =>
          simpa [fromCells, List.reverse_cons, List.map_append, List.append_assoc] using ht

theorem reverse (code : Program) (remaining packet : List Bool) :
    eval (step code) (remaining.length + 1) (.reversing remaining packet) =
      PMF.pure (.returned (remaining.reverse ++ packet)) := by
  induction remaining generalizing packet with
  | nil => simp [eval, step]
  | cons bit remaining ih =>
      rw [show (bit :: remaining).length + 1 = (remaining.length + 1) + 1 by rfl, eval]
      simp only [step, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Includes the ownership transfer from native halt and all head movements. -/
theorem run (code : Program) (machine : Configuration) (packet : List Bool)
    (hHalt : machine.halted = true) (hTape : machine.outputTape = endTape packet) :
    eval (step code) (3 * packet.length + 4) (.running machine) =
      PMF.pure (.returned packet) := by
  rw [show 3 * packet.length + 4 = (packet.length + 1) +
    ((packet.length + 1) + (packet.length + 1)) + 1 by omega, eval]
  simp only [step, hHalt, ↓reduceIte, PMF.pure_bind, hTape, endTape]
  rw [eval_add]
  have hr := rewind code (packet.reverse.map some) none []
  simp only [List.length_map, List.length_reverse, List.map_reverse,
    List.reverse_reverse] at hr
  simp only [List.map_reverse] at ⊢
  rw [hr, PMF.pure_bind, eval_add]
  have hc := collect code packet [] [] []
  simp only [List.append_nil] at hc
  have hc' : eval (step code) (packet.length + 1)
      (.collecting (fromCells (packet.map some ++ [none])) []) =
      PMF.pure (.reversing packet.reverse []) := by
    simpa only [fromCells] using hc
  rw [hc', PMF.pure_bind]
  simpa using reverse code packet.reverse []

/-- Export a packet whose head is already at its first cell. This is the
physical layout left by an interactive response loader. No tape reset or
semantic packet extraction is performed by the exporter. -/
theorem run_fromHead (code : Program) (machine : Configuration) (packet : List Bool)
    (hHalt : machine.halted = true)
    (hTape : machine.outputTape = fromCells (packet.map some ++ [none])) :
    eval (step code) (2 * packet.length + 4) (.running machine) =
      PMF.pure (.returned packet) := by
  rw [show 2 * packet.length + 4 = 1 + (1 + ((packet.length + 1) + (packet.length + 1))) by omega,
    eval_add]
  have first : eval (step code) 1 (.running machine) =
      PMF.pure (.rewinding (fromCells (packet.map some ++ [none]))) := by
    simp [eval, step, hHalt, hTape]
  rw [first, PMF.pure_bind, eval_add]
  have rewound : eval (step code) 1 (.rewinding (fromCells (packet.map some ++ [none]))) =
      PMF.pure (.collecting (fromCells (packet.map some ++ [none])) []) := by
    simp [eval, step, fromCells]
  rw [rewound, PMF.pure_bind, eval_add]
  have collected := collect code packet [] [] []
  simp only [List.append_nil] at collected
  have collected' : eval (step code) (packet.length + 1)
      (.collecting (fromCells (packet.map some ++ [none])) []) =
      PMF.pure (.reversing packet.reverse []) := by
    simpa only [fromCells] using collected
  rw [collected', PMF.pure_bind]
  simpa using reverse code packet.reverse []

variable {Input : Type u} {Output : Type v}

noncomputable def body (P : Machine.Procedure Input Output)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (read : Input → Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output) :
    TimedExecution.Procedure (step P.code) Input Output :=
  P.execution.liftBoundary Configuration.halted (fun input output _ => hHalt input output)
    (fun machine h => by simp [stepPMF, next, h]) read hRead
    (step P.code) boundary Control.running (fun _ => rfl)
    (fun machine h => by simp [step, h])

/-- The encoder describes a proved physical layout; runtime uses only tape cells. -/
noncomputable def delivery (P : Machine.Procedure Input Output) (encode : Output → List Bool)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (hTape : ∀ input output, (P.execution.exit input output).outputTape = endTape (encode output)) :
    TimedExecution.Procedure (step P.code) (Input × Output) Unit :=
  TimedExecution.Procedure.ofFixed (step P.code)
    (fun input => .running (P.execution.exit input.1 input.2))
    (fun input _ => .returned (encode input.2)) (fun _ => PMF.pure ())
    (fun input => 3 * (encode input.2).length + 4)
    (fun input => by
      simpa only [PMF.pure_map] using ResponseExport.run P.code (P.execution.exit input.1 input.2) (encode input.2)
        (hHalt input.1 input.2) (hTape input.1 input.2))

noncomputable def whole (P : Machine.Procedure Input Output) (encode : Output → List Bool)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (hTape : ∀ input output, (P.execution.exit input output).outputTape = endTape (encode output))
    (read : Input → Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (cap : Input → Nat)
    (hCap : ∀ input output, output ∈ (P.execution.semantics input).support →
      (encode output).length ≤ cap input) :=
  (body P hHalt read hRead).remember.seq (delivery P encode hHalt hTape)
    (fun _ _ _ => rfl) (fun input => 3 * cap input + 4)
    (fun input result hResult => by
      change result ∈ ((P.execution.semantics input).map (fun output => (input, output))).support at hResult
      rw [PMF.mem_support_map_iff] at hResult
      obtain ⟨output, hOutput, he⟩ := hResult
      subst result
      have h := hCap input output hOutput
      change 3 * (encode output).length + 4 ≤ 3 * cap input + 4
      omega)

theorem whole_run (P : Machine.Procedure Input Output) (encode : Output → List Bool)
    (hHalt : ∀ input output, (P.execution.exit input output).halted = true)
    (hTape : ∀ input output, (P.execution.exit input output).outputTape = endTape (encode output))
    (read : Input → Configuration → Output)
    (hRead : ∀ input output, read input (P.execution.exit input output) = output)
    (cap : Input → Nat)
    (hCap : ∀ input output, output ∈ (P.execution.semantics input).support →
      (encode output).length ≤ cap input)
    (input : Input) (horizon : Nat) (hBudget : P.execution.budget input + (3 * cap input + 4) ≤ horizon) :
    eval (step P.code) horizon (.running (P.execution.entry input)) =
      (P.execution.semantics input).map (fun output => .returned (encode output)) := by
  have h := (whole P encode hHalt hTape read hRead cap hCap).final_run input
    (fun _ _ => rfl) horizon hBudget
  simpa only [whole, body, delivery, TimedExecution.Procedure.seq,
    TimedExecution.Procedure.remember, TimedExecution.Procedure.liftBoundary,
    TimedExecution.Procedure.ofFixed, PMF.map, PMF.bind_bind, PMF.pure_bind,
    Function.comp_def] using h

end Machine.ResponseExport
