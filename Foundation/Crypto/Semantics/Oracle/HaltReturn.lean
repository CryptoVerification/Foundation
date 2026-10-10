import Foundation.Crypto.Semantics.Oracle.CodeRelocation
import Foundation.Crypto.Semantics.Oracle.NativeCode
import Foundation.Crypto.Semantics.BoundaryActiveCongruence

/-! A trace-certified return compiler for interactive code. Only native
halts are changed to a jump. Source addresses remain unchanged, so this
contract does not claim to repair fall-off termination or malformed jumps.
The verified active prefix and the actual final halt justify its use. -/
namespace CryptoOracle.Interactive.HaltReturn
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def instruction (address : Nat) : Instruction → Instruction
  | .native op => .native (if op = .halt then .jump address else op)
  | .call => .call

def host (source tail : Code) : Code :=
  source.map (instruction source.length) ++ tail.map (CodeRelocation.instruction source.length)

theorem source_lookup (source tail : Code) (pc : Nat) (inside : pc < source.length) :
    (host source tail)[pc]? = (source[pc]?).map (instruction source.length) := by
  unfold host
  rw [List.getElem?_append_left (by simpa only [List.length_map] using inside), List.getElem?_map]

theorem host_length (source tail : Code) : (host source tail).length = source.length + tail.length := by
  simp [host]

theorem active_step_of_fetch {State : Type*} (source target : Code)
    (same : ∀ (pc : Nat) (op : CryptoOracle.Interactive.Instruction), source[pc]? = some op → op ≠ .native .halt → target[pc]? = some op)
    (oracle : BitOracle State)
    (start : Configuration State) (active : Reification.terminal start.control = false)
    (nextActive : ∀ next ∈ (Reification.timedStep source oracle start).support,
      Reification.terminal next.control = false) :
    Reification.timedStep target oracle start = Reification.timedStep source oracle start := by
  rcases start with ⟨state, control, trace⟩
  cases control with
  | running machine =>
      have running : machine.halted = false := active
      cases lookup : source[machine.pc]? with
      | none =>
          have supported : (⟨state, .finished false, trace⟩ : Configuration State) ∈
              (Reification.timedStep source oracle ⟨state, .running machine, trace⟩).support := by
            simp [Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
              transition, running, lookup]
          have impossible := nextActive _ supported
          contradiction
      | some original =>
          cases original with
          | call =>
              have compiled := same machine.pc .call lookup (by simp)
              simp [Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
                transition, running, lookup, compiled]
          | native op =>
              by_cases stopped : op = .halt
              · subst op
                have supported : (NativeCode.frame state trace { machine with halted := true }) ∈
                    (Reification.timedStep source oracle ⟨state, .running machine, trace⟩).support := by
                  simp [Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
                    transition, running, lookup, NativeCode.frame, Machine.Instruction.next]
                have impossible := nextActive _ supported
                contradiction
              · have compiled := same machine.pc (.native op) lookup (by simpa using stopped)
                simp [Reification.timedStep, Reification.terminal, Reification.perform, Reification.action,
                  transition, running, lookup, compiled]
  | sending => rfl
  | reversing => rfl
  | awaiting => rfl
  | loading => rfl
  | advancing => rfl
  | rewinding => rfl
  | finished => rfl

theorem active_step {State : Type*} (source tail : Code) (oracle : BitOracle State)
    (start : Configuration State) (active : Reification.terminal start.control = false)
    (nextActive : ∀ next ∈ (Reification.timedStep source oracle start).support,
      Reification.terminal next.control = false) :
    Reification.timedStep (host source tail) oracle start = Reification.timedStep source oracle start := by
  apply active_step_of_fetch source (host source tail) _ oracle start active nextActive
  intro pc op fetched notHalt
  have inside : pc < source.length := by
    by_contra outside
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at fetched
    contradiction
  rw [source_lookup source tail pc inside, fetched]
  cases op with
  | call => rfl
  | native native => simp [instruction, show native ≠ .halt from by simpa using notHalt]

/-- Any target retaining all source nonhalt instructions preserves a
certified active prefix; halt targets may vary by source address. -/
theorem active_eval_of_fetch {State : Type*} (source target : Code)
    (same : ∀ (pc : Nat) (op : CryptoOracle.Interactive.Instruction), source[pc]? = some op → op ≠ .native .halt → target[pc]? = some op)
    (oracle : BitOracle State) (fuel : Nat) (start : Configuration State)
    (active : ∀ result ∈ (TimedExecution.eval (Reification.timedStep source oracle) fuel start).support,
      Reification.terminal result.control = false) :
    TimedExecution.eval (Reification.timedStep target oracle) fuel start =
      TimedExecution.eval (Reification.timedStep source oracle) fuel start := by
  exact eval_congr_of_active_final _ _ (fun frame => Reification.terminal frame.control)
    (by intro frame terminal; simp [Reification.timedStep, terminal])
    (active_step_of_fetch source target same oracle) fuel start active

/-- Only the already proved active source prefix is preserved. In
particular, no unproved global control-closure condition is assumed. -/
theorem active_eval {State : Type*} (source tail : Code) (oracle : BitOracle State)
    (fuel : Nat) (start : Configuration State)
    (active : ∀ result ∈ (TimedExecution.eval (Reification.timedStep source oracle) fuel start).support,
      Reification.terminal result.control = false) :
    TimedExecution.eval (Reification.timedStep (host source tail) oracle) fuel start =
      TimedExecution.eval (Reification.timedStep source oracle) fuel start := by
  exact eval_congr_of_active_final _ _ (fun frame => Reification.terminal frame.control)
    (by intro frame terminal; simp [Reification.timedStep, terminal])
    (active_step source tail oracle) fuel start active

/-- The final actual halt is compiled into a jump at the same transition
count. resumeAt describes the resulting frame; no host resume is executed. -/
theorem return_run {State : Type*} (source tail : Code) (oracle : BitOracle State)
    (state : State) (trace : List (List Bool × List Bool))
    (start before : Machine.Configuration) (fuel : Nat) (beforeActive : before.halted = false)
    (prefixRun : TimedExecution.eval (Reification.timedStep source oracle) fuel
      (NativeCode.frame state trace start) = PMF.pure (NativeCode.frame state trace before))
    (haltInstruction : source[before.pc]? = some (.native .halt)) :
    TimedExecution.eval (Reification.timedStep (host source tail) oracle) (fuel + 1)
      (NativeCode.frame state trace start) =
      PMF.pure (NativeCode.frame state trace (before.resumeAt source.length)) := by
  have inside : before.pc < source.length := by
    by_contra outside
    have absent : source[before.pc]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [absent] at haltInstruction
    contradiction
  have compiled := source_lookup source tail before.pc inside
  rw [haltInstruction] at compiled
  have unchanged := active_eval source tail oracle fuel (NativeCode.frame state trace start)
    (by intro frame support
        rw [prefixRun, PMF.mem_support_pure_iff] at support
        subst frame
        exact beforeActive)
  rw [TimedExecution.eval_add, unchanged, prefixRun, PMF.pure_bind]
  simp [TimedExecution.eval, Reification.timedStep, Reification.terminal, NativeCode.frame,
    Reification.perform, Reification.action, transition, beforeActive, compiled, instruction,
    Machine.Instruction.next, Configuration.resumeAt]

/-- After the actual return jump, the appended body uses the existing
relocation semantics, including all random and oracle transitions. -/
theorem body_eval {State : Type*} (source tail : Code) (oracle : BitOracle State)
    (fuel : Nat) (start : Configuration State) :
    TimedExecution.eval (Reification.timedStep (host source tail) oracle) fuel
      (CodeRelocation.frame source.length start) =
      (TimedExecution.eval (Reification.timedStep tail oracle) fuel start).map
        (CodeRelocation.frame source.length) := by
  simpa only [host, CodeRelocation.host, List.length_map] using
    CodeRelocation.eval (source.map (instruction source.length)) tail oracle fuel start

theorem host_native (source tail : Code)
    (hs : ∀ op ∈ source, ∃ native, op = .native native)
    (ht : ∀ op ∈ tail, ∃ native, op = .native native) :
    ∀ op ∈ host source tail, ∃ native, op = .native native := by
  intro op member
  simp only [host, List.mem_append, List.mem_map] at member
  rcases member with ⟨original, member, rfl⟩ | ⟨original, member, rfl⟩
  · obtain ⟨native, rfl⟩ := hs original member
    exact ⟨_, rfl⟩
  · obtain ⟨native, rfl⟩ := ht original member
    exact ⟨_, rfl⟩

/-- Each source halt may return to a different absolute target, chosen
statically from its address. Runtime tape contents never choose this map. -/
def returnPrefix (source : Code) (returnAt : Nat → Nat) : Code :=
  source.mapIdx (fun pc op => instruction (returnAt pc) op)

@[simp] theorem returnPrefix_length (source : Code) (returnAt : Nat → Nat) :
    (returnPrefix source returnAt).length = source.length := by simp [returnPrefix]

def hostWithReturns (source tail : Code) (returnAt : Nat → Nat) : Code :=
  CodeRelocation.host (returnPrefix source returnAt) tail

theorem returnPrefix_lookup (source : Code) (returnAt : Nat → Nat) (pc : Nat) :
    (returnPrefix source returnAt)[pc]? = (source[pc]?).map (instruction (returnAt pc)) := by
  simp [returnPrefix]

theorem hostWithReturns_lookup (source tail : Code) (returnAt : Nat → Nat) (pc : Nat)
    (inside : pc < source.length) :
    (hostWithReturns source tail returnAt)[pc]? = (source[pc]?).map (instruction (returnAt pc)) := by
  unfold hostWithReturns CodeRelocation.host
  rw [List.getElem?_append_left (by simpa using inside), returnPrefix_lookup]

theorem hostWithReturns_preserves (source tail : Code) (returnAt : Nat → Nat)
    (pc : Nat) (op : CryptoOracle.Interactive.Instruction) (fetched : source[pc]? = some op)
    (notHalt : op ≠ .native .halt) :
    (hostWithReturns source tail returnAt)[pc]? = some op := by
  have inside : pc < source.length := by
    by_contra outside
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at fetched
    contradiction
  rw [hostWithReturns_lookup source tail returnAt pc inside, fetched]
  cases op with
  | call => rfl
  | native native => simp [instruction, show native ≠ .halt from by simpa using notHalt]

/-- The actual last halt becomes the statically selected return jump,
without an extra transition or changes to tape/state/transcript. -/
theorem return_run_with_targets {State : Type*} (source tail : Code) (returnAt : Nat → Nat)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (start before : Machine.Configuration) (fuel : Nat) (beforeActive : before.halted = false)
    (prefixRun : TimedExecution.eval (Reification.timedStep source oracle) fuel
      (NativeCode.frame state trace start) = PMF.pure (NativeCode.frame state trace before))
    (haltInstruction : source[before.pc]? = some (.native .halt)) :
    TimedExecution.eval (Reification.timedStep (hostWithReturns source tail returnAt) oracle) (fuel + 1)
      (NativeCode.frame state trace start) =
      PMF.pure (NativeCode.frame state trace (before.resumeAt (returnAt before.pc))) := by
  have inside : before.pc < source.length := by
    by_contra outside
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at haltInstruction
    contradiction
  have fetched := hostWithReturns_lookup source tail returnAt before.pc inside
  rw [haltInstruction] at fetched
  have unchanged := active_eval_of_fetch source (hostWithReturns source tail returnAt)
    (hostWithReturns_preserves source tail returnAt) oracle fuel (NativeCode.frame state trace start)
    (by intro frame support
        rw [prefixRun, PMF.mem_support_pure_iff] at support
        subst frame
        exact beforeActive)
  rw [TimedExecution.eval_add, unchanged, prefixRun, PMF.pure_bind]
  simp [TimedExecution.eval, Reification.timedStep, Reification.terminal, NativeCode.frame,
    Reification.perform, Reification.action, transition, beforeActive, fetched, instruction,
    Machine.Instruction.next, Configuration.resumeAt]

theorem body_eval_with_targets {State : Type*} (source tail : Code) (returnAt : Nat → Nat)
    (oracle : BitOracle State) (fuel : Nat) (start : Configuration State) :
    TimedExecution.eval (Reification.timedStep (hostWithReturns source tail returnAt) oracle) fuel
      (CodeRelocation.frame source.length start) =
      (TimedExecution.eval (Reification.timedStep tail oracle) fuel start).map (CodeRelocation.frame source.length) := by
  simpa only [hostWithReturns, returnPrefix_length] using
    CodeRelocation.eval (returnPrefix source returnAt) tail oracle fuel start

theorem returnPrefix_native (source : Code) (returnAt : Nat → Nat)
    (hs : ∀ op ∈ source, ∃ native, op = .native native) :
    ∀ op ∈ returnPrefix source returnAt, ∃ native, op = .native native := by
  intro op member
  obtain ⟨pc, inside, eq⟩ := List.exists_of_mem_mapIdx member
  obtain ⟨native, same⟩ := hs source[pc] (List.getElem_mem inside)
  rw [← eq, same]
  exact ⟨_, rfl⟩

end CryptoOracle.Interactive.HaltReturn
