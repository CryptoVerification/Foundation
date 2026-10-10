import Foundation.Crypto.Semantics.Oracle.NativeCodeOracleIndependence
import Foundation.Crypto.Semantics.Machine.TapeEquivalence

/-! Native interactive execution respects physical tape-cell equivalence.
Both physical representations execute the same code. No normalization step
is introduced; state/history and the actual first-halt clock are preserved.
The restriction to native code is essential: controller rewinding can count
represented blank cells and therefore need not preserve this clock. -/
namespace CryptoOracle.Interactive.NativeCode
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

inductive CellEquivalent {State : Type*} : Configuration State → Configuration State → Prop where
  | running (state : State) (trace : List (List Bool × List Bool))
      (first second : Machine.Configuration) (same : first.Equivalent second) :
      CellEquivalent (frame state trace first) (frame state trace second)
  | finished (state : State) (trace : List (List Bool × List Bool)) (bit : Bool) :
      CellEquivalent ⟨state, .finished bit, trace⟩ ⟨state, .finished bit, trace⟩

theorem CellEquivalent.symm {State : Type*} {first second : Configuration State}
    (same : CellEquivalent first second) : CellEquivalent second first := by
  cases same with
  | running state trace first second same => exact .running state trace second first same.symm
  | finished state trace bit => exact .finished state trace bit

theorem CellEquivalent.trans {State : Type*} {first middle last : Configuration State}
    (left : CellEquivalent first middle) (right : CellEquivalent middle last) : CellEquivalent first last := by
  cases left with
  | running state trace first middle same =>
      cases right with
      | running _ _ _ last other => exact .running state trace first last ⟨same.1.trans other.1, same.2.1.trans other.2.1,
          same.2.2.1.trans other.2.2.1, same.2.2.2.trans other.2.2.2⟩
  | finished state trace bit => cases right; exact .finished state trace bit

theorem CellEquivalent.running_right {State : Type*} {first : Configuration State}
    (state : State) (trace : List (List Bool × List Bool)) (machine : Machine.Configuration)
    (same : CellEquivalent first (frame state trace machine)) :
    ∃ actual, first = frame state trace actual ∧ actual.Equivalent machine := by
  cases same with
  | running _ _ actual _ same => exact ⟨actual, rfl, same⟩

theorem CellEquivalent.terminal {State : Type*} {first second : Configuration State}
    (same : CellEquivalent first second) :
    Reification.terminal first.control = Reification.terminal second.control := by
  cases same with
  | running state trace first second same => exact same.2.1
  | finished => rfl

/-- Reuse the existing machine step theorem, including fair random bits.
Only the currently fetched instruction is used in the proof-side program. -/
theorem step_bind_eq_of_cellEquivalent {State α : Type*} (target : Code)
    (native : ∀ op ∈ target, ∃ instruction, op = .native instruction)
    (oracle : BitOracle State) (first second : Configuration State)
    (same : CellEquivalent first second) (k : Configuration State → PMF α)
    (respects : ∀ first second, CellEquivalent first second → k first = k second) :
    (Reification.timedStep target oracle first).bind k =
      (Reification.timedStep target oracle second).bind k := by
  cases same with
  | finished state trace bit => rfl
  | running state trace first second same =>
      by_cases halted : first.halted = true
      · have otherHalted : second.halted = true := same.2.1.symm.trans halted
        simpa only [Reification.timedStep, Reification.terminal, frame, halted, otherHalted,
          ↓reduceIte, PMF.pure_bind] using respects _ _ (.running state trace first second same)
      · have active : first.halted = false := by simpa using halted
        have otherActive : second.halted = false := same.2.1.symm.trans active
        cases lookup : target[first.pc]? with
        | none =>
            have otherLookup : target[second.pc]? = none := by simpa only [← same.1] using lookup
            simp [Reification.timedStep, Reification.terminal, frame, active, otherActive,
              Reification.perform, Reification.action, transition, lookup, otherLookup]
        | some op =>
            obtain ⟨instruction, rfl⟩ := native op (List.mem_of_getElem? lookup)
            let program : Machine.Program := List.replicate (first.pc + 1) instruction
            have inside : first.pc < program.length := by simp [program]
            have otherInside : second.pc < program.length := by simpa only [← same.1] using inside
            have source : program[first.pc]? = some instruction := by simp [program]
            have otherSource : program[second.pc]? = some instruction := by simpa only [← same.1] using source
            have otherLookup : target[second.pc]? = some (.native instruction) := by
              simpa only [← same.1] using lookup
            rw [running_step_of_lookup program target oracle state trace first inside active (by simp [source, lookup]),
              running_step_of_lookup program target oracle state trace second otherInside otherActive (by simp [otherSource, otherLookup]),
              PMF.bind_map, PMF.bind_map]
            exact Machine.stepPMF_bind_eq_of_equivalent program first second same
              (fun machine => k (frame state trace machine))
              (fun first second same => respects _ _ (.running state trace first second same))

theorem eval_bind_eq_of_cellEquivalent {State α : Type*} (target : Code)
    (native : ∀ op ∈ target, ∃ instruction, op = .native instruction)
    (oracle : BitOracle State) (fuel : Nat) (first second : Configuration State)
    (same : CellEquivalent first second) (k : Configuration State → PMF α)
    (respects : ∀ first second, CellEquivalent first second → k first = k second) :
    (TimedExecution.eval (Reification.timedStep target oracle) fuel first).bind k =
      (TimedExecution.eval (Reification.timedStep target oracle) fuel second).bind k := by
  induction fuel generalizing first second with
  | zero => simpa only [TimedExecution.eval, PMF.pure_bind] using respects first second same
  | succ fuel ih =>
      simp only [TimedExecution.eval, PMF.bind_bind]
      exact step_bind_eq_of_cellEquivalent target native oracle first second same _
        (fun first second same => ih first second same)

theorem eval_map_eq_of_cellEquivalent {State α : Type*} (target : Code)
    (native : ∀ op ∈ target, ∃ instruction, op = .native instruction)
    (oracle : BitOracle State) (fuel : Nat) (first second : Configuration State)
    (same : CellEquivalent first second) (observe : Configuration State → α)
    (respects : ∀ first second, CellEquivalent first second → observe first = observe second) :
    (TimedExecution.eval (Reification.timedStep target oracle) fuel first).map observe =
      (TimedExecution.eval (Reification.timedStep target oracle) fuel second).map observe := by
  exact eval_bind_eq_of_cellEquivalent target native oracle fuel first second same
    (fun frame => PMF.pure (observe frame)) (fun first second same => congrArg PMF.pure (respects first second same))

/-- The first native halt and its clock agree for every observation of cells.
This does not identify the concrete physical lists or their encoded lengths. -/
theorem first_bind_eq_of_cellEquivalent {State α : Type*} (target : Code)
    (native : ∀ op ∈ target, ∃ instruction, op = .native instruction)
    (oracle : BitOracle State) (fuel : Nat) (first second : Configuration State)
    (same : CellEquivalent first second) (k : Configuration State × Nat → PMF α)
    (respects : ∀ first second time, CellEquivalent first second → k (first, time) = k (second, time)) :
    (runToBoundary (Reification.timedStep target oracle) (fun frame => Reification.terminal frame.control) fuel first).bind k =
      (runToBoundary (Reification.timedStep target oracle) (fun frame => Reification.terminal frame.control) fuel second).bind k := by
  induction fuel generalizing first second k with
  | zero => simpa only [runToBoundary, PMF.pure_bind] using respects first second 0 same
  | succ fuel ih =>
      have terminal := same.terminal
      simp only [runToBoundary, ← terminal]
      split
      · simpa only [PMF.pure_bind] using respects first second 0 same
      · simp only [PMF.bind_bind, PMF.bind_map]
        apply step_bind_eq_of_cellEquivalent target native oracle first second same
        intro first second same
        exact ih first second same (fun result => k (result.1, result.2 + 1))
          (fun first second time same => respects first second (time + 1) same)

end CryptoOracle.Interactive.NativeCode
