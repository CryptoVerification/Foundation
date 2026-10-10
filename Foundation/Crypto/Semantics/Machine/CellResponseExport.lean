import Foundation.Crypto.Semantics.Machine.ResponseExport
import Foundation.Crypto.Semantics.Machine.NativeFirstArrivalContinuation

/-! Export an actual contiguous packet despite arbitrary represented outer
blank padding. Rewind inspects cells rather than the finite list boundary.
No normalization, semantic packet allocation or uncharged copy is performed.
The full physical input is used and each cell movement is a real transition. -/
namespace Machine.CellResponseExport
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

abbrev Control := ResponseExport.Control

noncomputable def step (code : Program) : Control → PMF Control
  | .running machine =>
      if machine.halted then PMF.pure (.rewinding machine.outputTape)
      else (stepPMF code machine).map .running
  | .rewinding tape =>
      if (tape.left.getD 0 none).isSome then PMF.pure (.rewinding tape.moveLeft)
      else PMF.pure (.collecting tape [])
  | .collecting tape reversed =>
      match tape.current with
      | none => PMF.pure (.reversing reversed [])
      | some bit => PMF.pure (.collecting tape.moveRight (bit :: reversed))
  | .reversing remaining packet =>
      match remaining with
      | [] => PMF.pure (.returned packet)
      | bit :: rest => PMF.pure (.reversing rest (bit :: packet))
  | .returned packet => PMF.pure (.returned packet)

private theorem blank_suffix (bits : List Bool) (cells : List (Option Bool))
    (h : ∀ i, cells.getD i none = (bits.map some).getD i none) :
    ∃ rest, cells = bits.map some ++ rest ∧ ∀ i, rest.getD i none = none := by
  induction bits generalizing cells with
  | nil => exact ⟨cells, rfl, by simpa using h⟩
  | cons bit bits ih =>
      have hHead := h 0
      cases cells with
      | nil => simp at hHead
      | cons cell cells =>
          have hc : cell = some bit := by simpa using hHead
          have ht : ∀ i, cells.getD i none = (bits.map some).getD i none := by
            intro i
            simpa only [List.map_cons, List.getD_cons_succ] using h (i + 1)
          obtain ⟨rest, hr, hb⟩ := ih cells ht
          exact ⟨rest, by simp [hc, hr], hb⟩

theorem rewind (code : Program) (left : List Bool) (before : List (Option Bool))
    (hBefore : before.getD 0 none = none) (current : Option Bool) (right : List (Option Bool)) :
    eval (step code) (left.length + 1) (.rewinding ⟨left.map some ++ before, current, right⟩) =
      PMF.pure (.collecting
        { (ResponseExport.fromCells (left.reverse.map some ++ current :: right)) with left := before } []) := by
  induction left generalizing current right with
  | nil =>
      have hb : before[0]?.getD none = none := hBefore
      simp [eval, step, hb, ResponseExport.fromCells]
  | cons bit left ih =>
      rw [show (bit :: left).length + 1 = (left.length + 1) + 1 by rfl, eval]
      simp only [step, List.map_cons, List.cons_append, List.getD_cons_zero, Option.isSome_some,
        ↓reduceIte, Tape.moveLeft, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem collect (code : Program) (packet reversed : List Bool) (tail before : List (Option Bool)) :
    eval (step code) (packet.length + 1)
      (.collecting { (ResponseExport.fromCells (packet.map some ++ none :: tail)) with left := before } reversed) =
      PMF.pure (.reversing (packet.reverse ++ reversed) []) := by
  induction packet generalizing reversed before with
  | nil => simp [eval, step, ResponseExport.fromCells]
  | cons bit packet ih =>
      rw [show (bit :: packet).length + 1 = (packet.length + 1) + 1 by rfl, eval]
      simp only [step, ResponseExport.fromCells, List.map_cons, List.cons_append, List.headD_cons,
        List.tail_cons, Tape.moveRight, PMF.pure_bind]
      cases packet <;> simpa [ResponseExport.fromCells, List.reverse_cons, List.map_append, List.append_assoc]
        using ih (bit :: reversed) (some bit :: before)

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

/-- The scan observes current/right cells, retaining every represented
blank in the actual tape. Each supported bit is read by a real transition. -/
theorem collect_equivalent (code : Program) (packet reversed : List Bool)
    (tail before : List (Option Bool)) (tape : Tape)
    (layout : tape.Equivalent
      { (ResponseExport.fromCells (packet.map some ++ none :: tail)) with left := before }) :
    eval (step code) (packet.length + 1) (.collecting tape reversed) =
      PMF.pure (.reversing (packet.reverse ++ reversed) []) := by
  induction packet generalizing tape before reversed with
  | nil =>
      have current : tape.current = none := layout.1
      simp [eval, step, current]
  | cons bit rest ih =>
      have current : tape.current = some bit := layout.1
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by simp; omega, eval_add]
      have first : eval (step code) 1 (.collecting tape reversed) =
          PMF.pure (.collecting tape.moveRight (bit :: reversed)) := by simp [eval, step, current]
      rw [first, PMF.pure_bind]
      have next : tape.moveRight.Equivalent
          { (ResponseExport.fromCells (rest.map some ++ none :: tail)) with left := some bit :: before } := by
        have h := layout.moveRight
        cases rest <;> simpa [ResponseExport.fromCells, Tape.moveRight] using h
      rw [ih (bit :: reversed) (some bit :: before) tape.moveRight next]
      simp [List.reverse_cons, List.append_assoc]

/-- Export directly from a cell-equivalent first-cell layout. The rewind
inspects the adjacent blank cell, not the length of the finite left list. -/
theorem run_fromHead_withPrefix (code : Program) (machine : Configuration) (packet : List Bool)
    (before tail : List (Option Bool)) (blank : before.getD 0 none = none)
    (halted : machine.halted = true)
    (layout : machine.outputTape.Equivalent { (ResponseExport.fromCells (packet.map some ++ none :: tail)) with left := before }) :
    eval (step code) (2 * packet.length + 4) (.running machine) =
      PMF.pure (.returned packet) := by
  have left : machine.outputTape.left[0]?.getD none = none := (layout.2.1 0).trans blank
  rw [show 2 * packet.length + 4 = 1 + (1 + ((packet.length + 1) + (packet.length + 1))) by omega, eval_add]
  have first : eval (step code) 1 (.running machine) = PMF.pure (.rewinding machine.outputTape) := by
    simp [eval, step, halted]
  rw [first, PMF.pure_bind, eval_add]
  have rewound : eval (step code) 1 (.rewinding machine.outputTape) =
      PMF.pure (.collecting machine.outputTape []) := by simp [eval, step, left]
  rw [rewound, PMF.pure_bind, eval_add]
  have collected := collect_equivalent code packet [] tail before machine.outputTape layout
  simp only [List.append_nil] at collected
  rw [collected, PMF.pure_bind]
  simpa using reverse code packet.reverse []

theorem run_fromHead (code : Program) (machine : Configuration) (packet : List Bool)
    (halted : machine.halted = true)
    (layout : machine.outputTape.Equivalent (ResponseExport.fromCells (packet.map some ++ [none]))) :
    eval (step code) (2 * packet.length + 4) (.running machine) =
      PMF.pure (.returned packet) := by
  exact run_fromHead_withPrefix code machine packet [] [] rfl halted layout

/-- Cell-equivalent padding is retained during traversal, not replaced by
an ideal finite representative. Export stops at the first blank boundary. -/
theorem run (code : Program) (machine : Configuration) (packet : List Bool)
    (hHalt : machine.halted = true) (hTape : machine.outputTape.Equivalent (ResponseExport.endTape packet)) :
    eval (step code) (3 * packet.length + 4) (.running machine) = PMF.pure (.returned packet) := by
  obtain ⟨before, hLeft, hBefore⟩ := blank_suffix packet.reverse machine.outputTape.left hTape.2.1
  have hCurrent : machine.outputTape.current = none := hTape.1
  have hLayout : machine.outputTape = ⟨packet.reverse.map some ++ before, none, machine.outputTape.right⟩ := by
    generalize ht : machine.outputTape = tape at hLeft hCurrent ⊢
    cases tape
    simp_all
  rw [show 3 * packet.length + 4 = (packet.length + 1) + ((packet.length + 1) + (packet.length + 1)) + 1 by omega, eval]
  simp only [step, hHalt, ↓reduceIte, PMF.pure_bind]
  rw [hLayout]
  rw [eval_add]
  have hr := rewind code packet.reverse before (hBefore 0) none machine.outputTape.right
  simp only [List.length_reverse, List.reverse_reverse] at hr
  rw [hr, PMF.pure_bind, eval_add, collect, PMF.pure_bind]
  simpa using reverse code packet.reverse []

/-- After moving all bits, the explicit return transition is still pending. -/
theorem reverse_before_return (code : Program) (remaining packet : List Bool) :
    eval (step code) remaining.length (.reversing remaining packet) =
      PMF.pure (.reversing [] (remaining.reverse ++ packet)) := by
  induction remaining generalizing packet with
  | nil => simp [eval]
  | cons bit remaining ih =>
      rw [show (bit :: remaining).length = remaining.length + 1 by rfl, eval]
      simp only [step, PMF.pure_bind]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

/-- One transition before the certified horizon, export has not returned.
This retains arbitrary cell-equivalent blank padding at the input. -/
theorem run_before_return (code : Program) (machine : Configuration) (packet : List Bool)
    (hHalt : machine.halted = true) (hTape : machine.outputTape.Equivalent (ResponseExport.endTape packet)) :
    eval (step code) (3 * packet.length + 3) (.running machine) =
      PMF.pure (.reversing [] packet) := by
  obtain ⟨before, hLeft, hBefore⟩ := blank_suffix packet.reverse machine.outputTape.left hTape.2.1
  have hCurrent : machine.outputTape.current = none := hTape.1
  have hLayout : machine.outputTape = ⟨packet.reverse.map some ++ before, none, machine.outputTape.right⟩ := by
    generalize ht : machine.outputTape = tape at hLeft hCurrent ⊢
    cases tape
    simp_all
  rw [show 3 * packet.length + 3 = (packet.length + 1) + ((packet.length + 1) + packet.length) + 1 by omega, eval]
  simp only [step, hHalt, ↓reduceIte, PMF.pure_bind]
  rw [hLayout, eval_add]
  have hr := rewind code packet.reverse before (hBefore 0) none machine.outputTape.right
  simp only [List.length_reverse, List.reverse_reverse] at hr
  rw [hr, PMF.pure_bind, eval_add, collect, PMF.pure_bind]
  simpa using reverse_before_return code packet.reverse []

structure Input where
  machine : Configuration
  packet : List Bool
  halted : machine.halted = true
  layout : machine.outputTape.Equivalent (ResponseExport.endTape packet)

noncomputable def procedure (code : Program) : TimedExecution.Procedure (step code) Input (List Bool) :=
  TimedExecution.Procedure.ofFixed (step code) (fun input => .running input.machine)
    (fun _ packet => .returned packet) (fun input => PMF.pure input.packet)
    (fun input => 3 * input.packet.length + 4) (fun input => by
      simpa only [PMF.pure_map] using run code input.machine input.packet input.halted input.layout)

end Machine.CellResponseExport
