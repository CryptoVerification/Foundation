import Foundation.Crypto.Semantics.Oracle.NativePacketComponent
import Foundation.Crypto.Semantics.Oracle.NativeCodeOracleIndependence

/-! Native-only computation followed by physical export never invokes the
external oracle. This includes every intermediate exporter state. -/
namespace CryptoOracle.Interactive.NativePacketComponent
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def nativeControl {State : Type*} : Control State → Prop
  | .computing frame => NativeCode.nativeControl frame.control
  | .exporting _ _ => True

/-- Loading and its local tape movement are allowed as well as native
execution. Sending and awaiting external capabilities remain excluded. -/
def localControl {State : Type*} : Control State → Prop
  | .computing frame => NativeCode.localControl frame.control
  | .exporting _ _ => True

theorem nativeControl_local {State : Type*} (start : Control State)
    (valid : nativeControl start) : localControl start := by
  cases start with
  | computing frame => exact NativeCode.nativeControl_local valid
  | exporting => trivial

theorem local_only_step {State : Type*} (code : Code)
    (native : ∀ instruction ∈ code, ∃ op, instruction = .native op)
    (first second : BitOracle State) (start : Control State) (valid : localControl start) :
    step code first start = step code second start ∧
    ∀ next ∈ (step code first start).support, localControl next := by
  cases start with
  | computing frame =>
      by_cases terminal : Reification.terminal frame.control = true
      · constructor
        · simp only [step, terminal, ↓reduceIte]
        · intro next supported
          simp only [step, terminal, ↓reduceIte] at supported
          cases hc : frame.control <;>
            simp only [hc, PMF.mem_support_pure_iff] at supported <;>
            subst next <;> trivial
      · have h := NativeCode.local_only_step code native first second frame valid
        constructor
        · simp only [step, terminal, Bool.false_eq_true, ↓reduceIte, h.1]
        · intro next supported
          simp only [step, terminal, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at supported
          obtain ⟨frameNext, support, rfl⟩ := supported
          exact h.2 frameNext support
  | exporting frame exporter =>
      constructor
      · rfl
      · intro next supported
        simp only [step, PMF.mem_support_map_iff] at supported
        obtain ⟨exporterNext, _, rfl⟩ := supported
        trivial

theorem local_only_eval {State : Type*} (code : Code)
    (native : ∀ instruction ∈ code, ∃ op, instruction = .native op)
    (first second : BitOracle State) (fuel : Nat) (start : Control State) (valid : localControl start) :
    TimedExecution.eval (step code first) fuel start =
      TimedExecution.eval (step code second) fuel start := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      have h := local_only_step code native first second start valid
      simp only [TimedExecution.eval]
      rw [← h.1, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext next support
      exact ih next (h.2 next support)

/-- Retain the stronger native-only support guarantee for existing users. -/
theorem native_only_step {State : Type*} (code : Code)
    (native : ∀ instruction ∈ code, ∃ op, instruction = .native op)
    (first second : BitOracle State) (start : Control State) (valid : nativeControl start) :
    step code first start = step code second start ∧
    ∀ next ∈ (step code first start).support, nativeControl next := by
  cases start with
  | computing frame =>
      by_cases terminal : Reification.terminal frame.control = true
      · constructor
        · simp only [step, terminal, ↓reduceIte]
        · intro next supported
          simp only [step, terminal, ↓reduceIte] at supported
          cases hc : frame.control <;>
            simp only [hc, PMF.mem_support_pure_iff] at supported <;>
            subst next <;> trivial
      · have h := NativeCode.native_only_step code native first second frame valid
        constructor
        · simp only [step, terminal, Bool.false_eq_true, ↓reduceIte, h.1]
        · intro next supported
          simp only [step, terminal, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_map_iff] at supported
          obtain ⟨frameNext, support, rfl⟩ := supported
          exact h.2 frameNext support
  | exporting frame exporter =>
      constructor
      · rfl
      · intro next supported
        simp only [step, PMF.mem_support_map_iff] at supported
        obtain ⟨exporterNext, _, rfl⟩ := supported
        trivial

theorem native_only_eval {State : Type*} (code : Code)
    (native : ∀ instruction ∈ code, ∃ op, instruction = .native op)
    (first second : BitOracle State) (fuel : Nat) (start : Control State) (valid : nativeControl start) :
    TimedExecution.eval (step code first) fuel start =
      TimedExecution.eval (step code second) fuel start :=
  local_only_eval code native first second fuel start (nativeControl_local start valid)

end CryptoOracle.Interactive.NativePacketComponent
