import Foundation.Crypto.Semantics.Machine.SubroutineSimulation
import Foundation.Crypto.Semantics.Oracle.ReificationExecution
import Foundation.Crypto.Semantics.ProcedureSimulation
import Foundation.Crypto.Semantics.Oracle.SourceStorage

/-! Embed a whole interactive caller after a finite leading instruction list. All absolute
branch and jump targets are shifted; tapes, responses and histories are kept.
No transfer instruction or synthetic halt is inserted by this analysis. -/
namespace CryptoOracle.Interactive.CodeRelocation
open Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false

def native (base : Nat) : Machine.Instruction → Machine.Instruction
  | .jump target => .jump (base + target)
  | .branch tape blank zero one => .branch tape (base + blank) (base + zero) (base + one)
  | instruction => instruction

def instruction (base : Nat) : Instruction → Instruction
  | .native original => .native (native base original)
  | .call => .call

def host (before code : Code) : Code := before ++ code.map (instruction before.length)

theorem lookup (before code : Code) (pc : Nat) :
    (host before code)[before.length + pc]? = (code[pc]?).map (instruction before.length) := by
  unfold host
  rw [List.getElem?_append_right (by omega)]
  simp

theorem native_next (base : Nat) (original : Machine.Instruction) (machine : Machine.Configuration) :
    (native base original).next (machine.rebasePc base) =
      Machine.rebaseStepResult base (original.next machine) := by
  cases original <;> cases machine <;>
    simp [native, Machine.Instruction.next, Machine.Configuration.rebasePc,
      Machine.rebaseStepResult, Machine.Configuration.advance, Machine.Configuration.updateTape,
      Machine.Configuration.tape]
  all_goals split <;> simp [Machine.Configuration.rebasePc, Nat.add_assoc]

def control (base : Nat) : Control → Control
  | .running machine => .running (machine.rebasePc base)
  | .sending machine tape reversed => .sending (machine.rebasePc base) tape reversed
  | .reversing machine remaining request => .reversing (machine.rebasePc base) remaining request
  | .awaiting machine request => .awaiting (machine.rebasePc base) request
  | .loading machine remaining tape => .loading (machine.rebasePc base) remaining tape
  | .advancing machine remaining tape => .advancing (machine.rebasePc base) remaining tape
  | .rewinding machine tape => .rewinding (machine.rebasePc base) tape
  | .finished bit => .finished bit

def frame {State : Type u} (base : Nat) (source : Configuration State) : Configuration State :=
  { source with control := control base source.control }

def transitionResult {State : Type u} (base : Nat) : Transition State → Transition State
  | .deterministic next => .deterministic (frame base next)
  | .random zero one => .random (frame base zero) (frame base one)
  | .oracleCall machine request => .oracleCall (machine.rebasePc base) request

theorem transition_eq {State : Type u} (before code : Code) (source : Configuration State) :
    transition (host before code) (frame before.length source) =
      transitionResult before.length (transition code source) := by
  rcases source with ⟨state, sourceControl, trace⟩
  cases sourceControl with
  | running machine =>
      cases hh : machine.halted with
      | true => simp [transition, frame, control, transitionResult, Machine.Configuration.rebasePc, hh]
      | false =>
          simp only [frame, control, transition, Machine.Configuration.rebasePc, hh, Bool.false_eq_true, ↓reduceIte]
          rw [lookup]
          cases hi : code[machine.pc]? with
          | none => simp [transitionResult, frame, control]
          | some original =>
              cases original with
              | call =>
                  simp [instruction, transitionResult, frame, control, Machine.Configuration.rebasePc,
                    Machine.Configuration.advance, Nat.add_assoc, hh]
              | native original =>
                  simp only [Option.map_some, instruction]
                  have hn := native_next before.length original machine
                  simp only [Machine.Configuration.rebasePc, hh] at hn
                  rw [hn]
                  cases original.next machine <;> rfl
  | sending machine tape reversed =>
      cases ht : tape.current <;> simp [transition, frame, control, transitionResult, ht]
  | reversing machine remaining request =>
      cases remaining <;> simp [transition, frame, control, transitionResult]
  | awaiting machine request => rfl
  | loading machine remaining tape =>
      cases remaining <;> simp [transition, frame, control, transitionResult]
  | advancing machine remaining tape => rfl
  | rewinding machine tape =>
      cases hl : tape.left <;> simp [transition, frame, control, transitionResult, Machine.Configuration.rebasePc, hl]
  | finished bit => rfl

theorem terminal (base : Nat) (source : Control) :
    Reification.terminal (control base source) = Reification.terminal source := by
  cases source <;> rfl

/-- Every source transition, including randomized and oracle transitions,
is preserved by placement after the leading instruction list. -/
theorem timed_step {State : Type u} (before code : Code) (oracle : BitOracle State)
    (source : Configuration State) :
    Reification.timedStep (host before code) oracle (frame before.length source) =
      (Reification.timedStep code oracle source).map (frame before.length) := by
  simp only [Reification.timedStep, frame, terminal]
  by_cases ht : Reification.terminal source.control = true
  · simp [ht, PMF.pure_map, frame]
  · simp only [ht, Bool.false_eq_true, ↓reduceIte]
    unfold Reification.perform Reification.action
    have hTransition := transition_eq before code (show Configuration Unit from ⟨(), source.control, []⟩)
    simp only [frame] at hTransition
    dsimp only
    rw [hTransition]
    cases h : transition code ⟨(), source.control, []⟩ with
    | deterministic next => simp [transitionResult, frame, PMF.pure_map]
    | random zero one =>
        simp only [transitionResult, PMF.map_comp, Function.comp_def]
        congr 1
        funext bit
        cases bit <;> rfl
    | oracleCall machine request =>
        simp only [transitionResult, PMF.map_comp, Function.comp_def]
        rfl

theorem eval {State : Type u} (before code : Code) (oracle : BitOracle State)
    (fuel : Nat) (source : Configuration State) :
    TimedExecution.eval (Reification.timedStep (host before code) oracle) fuel (frame before.length source) =
      (TimedExecution.eval (Reification.timedStep code oracle) fuel source).map (frame before.length) := by
  symm
  exact eval_map _ _ (frame before.length) (fun source => (timed_step before code oracle source).symm) fuel source

theorem code_length (before code : Code) : (host before code).length = before.length + code.length := by
  simp [host]

/-- All retained tapes and temporary lists have the same size. Finite code
and the representation of program-counter integers are separate resources. -/
theorem control_cells (base : Nat) (source : Control) :
    SourceStorage.controlCells (control base source) = SourceStorage.controlCells source := by
  cases source <;> rfl

theorem cells {State : Type u} (stateSize : State → Nat) (base : Nat) (source : Configuration State) :
    SourceStorage.cells stateSize (frame base source) = SourceStorage.cells stateSize source := by
  simp only [SourceStorage.cells, frame, control_cells]

noncomputable def procedure {State : Type u} {Input Output : Type*} (before code : Code)
    (oracle : BitOracle State) (P : Procedure (Reification.timedStep code oracle) Input Output) :=
  P.transport (Reification.timedStep (host before code) oracle) (frame before.length)
    (timed_step before code oracle)

theorem procedure_budget {State : Type u} {Input Output : Type*} (before code : Code)
    (oracle : BitOracle State) (P : Procedure (Reification.timedStep code oracle) Input Output) (input : Input) :
    (procedure before code oracle P).budget input = P.budget input := rfl

theorem procedure_costed {State : Type u} {Input Output : Type*} (before code : Code)
    (oracle : BitOracle State) (P : Procedure (Reification.timedStep code oracle) Input Output) (input : Input) :
    (procedure before code oracle P).costed input = P.costed input := rfl

end CryptoOracle.Interactive.CodeRelocation
