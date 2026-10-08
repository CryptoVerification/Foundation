import Foundation.Crypto.Semantics.Machine.DelimitedResponseLoading
import Foundation.Crypto.Semantics.Machine.StructuredCodeEncoding

/-! Whole-prefix storage for the cell-by-cell response loader. Both physical
tapes (including blanks), the unconsumed response, and its pending bit are
represented. The encoding is faithful and is not a runtime instruction. -/
namespace Machine.DelimitedResponseLoading.Resources
open Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

abbrev Fields := Nat × Configuration × List Bool × Bool

def pack : Control → Fields
  | .flag machine rest => (0, machine, rest, false)
  | .moveFlag machine bit rest => (1, machine, rest, bit)
  | .payload machine bit rest => (2, machine, rest, bit)
  | .movePayload machine rest => (3, machine, rest, false)
  | .terminate machine => (4, machine, [], false)
  | .done machine => (5, machine, [], false)

def unpack (fields : Fields) : Control :=
  match fields.1 with
  | 0 => .flag fields.2.1 fields.2.2.1
  | 1 => .moveFlag fields.2.1 fields.2.2.2 fields.2.2.1
  | 2 => .payload fields.2.1 fields.2.2.2 fields.2.2.1
  | 3 => .movePayload fields.2.1 fields.2.2.1
  | 4 => .terminate fields.2.1
  | _ => .done fields.2.1

def fieldsEncoding : FiniteBitEncoding Fields :=
  ConfigurationEncoding.unary.prod (ConfigurationEncoding.configuration.prod
    (FiniteBitEncoding.bitstring.prod ConfigurationEncoding.bit))

def encoding : FiniteBitEncoding Control := fieldsEncoding.retract pack unpack (by intro state; cases state <;> rfl)

def machine (state : Control) : Configuration := (pack state).2.1

def remaining (state : Control) : List Bool := (pack state).2.2.1

def extent (state : Control) : Nat := (machine state).tapeCells + (remaining state).length

theorem write_cells (state : Configuration) (bit : Bool) : (write state bit).tapeCells = state.tapeCells := by
  simp [write, Configuration.advance, Configuration.updateTape, Configuration.tapeCells, Tape.cells_write]

theorem move_cells (state : Configuration) : (move state).tapeCells ≤ state.tapeCells + 1 := by
  have h := Tape.cells_moveRight_le state.inputTape
  simp only [move, Configuration.advance, Configuration.updateTape, Configuration.tapeCells]
  omega

theorem step_bounds (start next : Control) (h : next ∈ (step start).support) :
    (machine next).pc ≤ (machine start).pc + 1 ∧ extent next ≤ extent start + 1 := by
  cases start with
  | flag state rest =>
      cases rest <;> simp only [step, PMF.mem_support_pure_iff] at h <;> subst next
      all_goals
        simp only [machine, remaining, pack, extent, List.length_nil, List.length_cons, write_cells]
        constructor
        · simp [write, Configuration.advance, Configuration.updateTape]
        · omega
  | moveFlag state bit rest =>
      simp only [step, PMF.mem_support_pure_iff] at h
      subst next
      have hCells := move_cells state
      simp only [machine, remaining, pack, extent]
      constructor
      · simp [move, Configuration.advance, Configuration.updateTape]
      · omega
  | payload state bit rest =>
      simp only [step, PMF.mem_support_pure_iff] at h
      subst next
      simp only [machine, remaining, pack, extent, write_cells]
      constructor
      · simp [write, Configuration.advance, Configuration.updateTape]
      · omega
  | movePayload state rest =>
      simp only [step, PMF.mem_support_pure_iff] at h
      subst next
      have hCells := move_cells state
      simp only [machine, remaining, pack, extent]
      constructor
      · simp [move, Configuration.advance, Configuration.updateTape]
      · omega
  | terminate state =>
      simp only [step, PMF.mem_support_pure_iff] at h
      subst next
      have hCells := move_cells state
      simp only [machine, remaining, pack, extent, List.length_nil, Nat.add_zero]
      constructor
      · simp [move, Configuration.advance, Configuration.updateTape]
      · exact hCells
  | done state =>
      simp only [step, PMF.mem_support_pure_iff] at h
      subst next
      exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩

theorem encoding_length (state : Control) :
    (encoding.encode state).length ≤ 4 * (machine state).pc + 36 * extent state + 42 := by
  have hConfiguration := ConfigurationEncoding.configuration_length_le (machine state)
  have hTag : (pack state).1 ≤ 5 := by cases state <;> simp [pack]
  change (fieldsEncoding.encode ((pack state).1, (pack state).2.1, (pack state).2.2.1, (pack state).2.2.2)).length ≤ _
  simp only [fieldsEncoding, FiniteBitEncoding.prod_encode_length, ConfigurationEncoding.unary,
    List.length_replicate, FiniteBitEncoding.bitstring, ConfigurationEncoding.bit, id_eq, List.length_singleton]
  unfold extent machine remaining at *
  omega

theorem peak (horizon elapsed : Nat) (hElapsed : elapsed ≤ horizon) (start state : Control)
    (h : state ∈ (eval step elapsed start).support) :
    (encoding.encode state).length ≤ 4 * ((machine start).pc + horizon) + 36 * (extent start + horizon) + 42 := by
  have hPc := ResourceGrowth.prefix_bound step (fun state => (machine state).pc) 1
    (fun before after hs => (step_bounds before after hs).1) horizon elapsed hElapsed start state h
  have hCells := ResourceGrowth.prefix_bound step extent 1
    (fun before after hs => (step_bounds before after hs).2) horizon elapsed hElapsed start state h
  have hEncoding := encoding_length state
  simp only [Nat.mul_one] at hPc hCells
  omega

end Machine.DelimitedResponseLoading.Resources
