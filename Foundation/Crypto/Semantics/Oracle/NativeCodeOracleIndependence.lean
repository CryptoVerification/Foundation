import Foundation.Crypto.Semantics.Oracle.NativeCode

/-! Native-only finite code does not invoke an external oracle, even when
it falls off malformed code. The supported public controls remain native
or finished; this connects resource analysis with an inert capability to
execution with an arbitrary unused capability. -/
namespace CryptoOracle.Interactive.NativeCode
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def nativeControl : Control → Prop
  | .running _ => True
  | .finished _ => True
  | _ => False

theorem native_only_step {State : Type*} (code : Code)
    (native : ∀ instruction ∈ code, ∃ machineInstruction, instruction = .native machineInstruction)
    (first second : BitOracle State) (start : Configuration State)
    (valid : nativeControl start.control) :
    Reification.timedStep code first start = Reification.timedStep code second start ∧
    ∀ next ∈ (Reification.timedStep code first start).support, nativeControl next.control := by
  rcases start with ⟨state, control, trace⟩
  cases control with
  | finished bit => simp [Reification.timedStep, Reification.terminal, nativeControl]
  | running machine =>
      by_cases halted : machine.halted = true
      · simp [Reification.timedStep, Reification.terminal, halted, nativeControl]
      · have active : machine.halted = false := by simpa using halted
        cases lookup : code[machine.pc]? with
        | none =>
            simp [Reification.timedStep, Reification.terminal, Reification.perform,
              Reification.action, transition, active, lookup, nativeControl]
        | some instruction =>
            rcases native instruction (List.mem_of_getElem? lookup) with ⟨machineInstruction, rfl⟩
            cases successor : machineInstruction.next machine with
            | inl next =>
                simp [Reification.timedStep, Reification.terminal, Reification.perform,
                  Reification.action, transition, active, lookup, successor, nativeControl]
            | inr pair =>
                constructor
                · simp [Reification.timedStep, Reification.terminal, Reification.perform,
                    Reification.action, transition, active, lookup, successor]
                · intro next support
                  simp only [Reification.timedStep, Reification.terminal, active, Bool.false_eq_true,
                    ↓reduceIte, Reification.perform, Reification.action, transition, lookup, successor,
                    PMF.mem_support_map_iff] at support
                  obtain ⟨bit, _, rfl⟩ := support
                  cases bit <;> trivial
  | sending => contradiction
  | reversing => contradiction
  | awaiting => contradiction
  | loading => contradiction
  | advancing => contradiction
  | rewinding => contradiction

/-- Local loading controls also cannot invoke a capability. This wider
invariant is separate so the original native-only support guarantee remains
unchanged. Sending, reversing a request, and awaiting are excluded. -/
def localControl : Control → Prop
  | .running _ | .finished _ | .loading _ _ _ | .advancing _ _ _ | .rewinding _ _ => True
  | _ => False

theorem nativeControl_local {control : Control} (valid : nativeControl control) : localControl control := by
  cases control <;> trivial

theorem local_only_step {State : Type*} (code : Code)
    (native : ∀ instruction ∈ code, ∃ machineInstruction, instruction = .native machineInstruction)
    (first second : BitOracle State) (start : Configuration State)
    (valid : localControl start.control) :
    Reification.timedStep code first start = Reification.timedStep code second start ∧
    ∀ next ∈ (Reification.timedStep code first start).support, localControl next.control := by
  rcases start with ⟨state, control, trace⟩
  cases control with
  | running machine =>
      have old := native_only_step code native first second ⟨state, .running machine, trace⟩ (by trivial)
      exact ⟨old.1, fun next support => nativeControl_local (old.2 next support)⟩
  | finished bit =>
      have old := native_only_step code native first second ⟨state, .finished bit, trace⟩ (by trivial)
      exact ⟨old.1, fun next support => nativeControl_local (old.2 next support)⟩
  | loading machine remaining tape =>
      cases remaining <;> simp [Reification.timedStep, Reification.terminal, Reification.perform,
        Reification.action, transition, localControl]
  | advancing machine remaining tape =>
      simp [Reification.timedStep, Reification.terminal, Reification.perform,
        Reification.action, transition, localControl]
  | rewinding machine tape =>
      cases left : tape.left <;> simp [Reification.timedStep, Reification.terminal, Reification.perform,
        Reification.action, transition, left, localControl]
  | sending => contradiction
  | reversing => contradiction
  | awaiting => contradiction

theorem local_only_eval {State : Type*} (code : Code)
    (native : ∀ instruction ∈ code, ∃ machineInstruction, instruction = .native machineInstruction)
    (first second : BitOracle State) (fuel : Nat) (start : Configuration State)
    (valid : localControl start.control) :
    TimedExecution.eval (Reification.timedStep code first) fuel start =
      TimedExecution.eval (Reification.timedStep code second) fuel start := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      have step := local_only_step code native first second start valid
      simp only [TimedExecution.eval]
      rw [← step.1, ← PMF.bindOnSupport_eq_bind, ← PMF.bindOnSupport_eq_bind]
      congr 1
      funext next support
      exact ih next (step.2 next support)

/-- All intermediate distributions agree for arbitrary external capabilities;
only native instructions are executed. Private state and histories are part
of the full public configuration, not merely its decoded observation. -/
theorem native_only_eval {State : Type*} (code : Code)
    (native : ∀ instruction ∈ code, ∃ machineInstruction, instruction = .native machineInstruction)
    (first second : BitOracle State) (fuel : Nat) (start : Configuration State)
    (valid : nativeControl start.control) :
    TimedExecution.eval (Reification.timedStep code first) fuel start =
      TimedExecution.eval (Reification.timedStep code second) fuel start := by
  exact local_only_eval code native first second fuel start (nativeControl_local valid)

end CryptoOracle.Interactive.NativeCode
