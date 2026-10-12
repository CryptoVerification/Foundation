import Foundation.Crypto.Semantics.Oracle.HaltReturn

/-! Replace only selected native halt sites by an executed jump. Other halts
remain stopping points; every nonhalt instruction and source address is retained. -/
namespace CryptoOracle.Interactive.SelectiveHaltReturn
open Machine Foundation.Probability TimedExecution
set_option backward.isDefEq.respectTransparency false

def instruction (target : Nat) (returns : Nat → Bool) (pc : Nat) (op : Instruction) : Instruction :=
  if returns pc then HaltReturn.instruction target op else op

def code (source : Code) (target : Nat) (returns : Nat → Bool) : Code :=
  source.mapIdx (fun pc op => instruction target returns pc op)

theorem code_length (source : Code) (target : Nat) (returns : Nat → Bool) :
    (code source target returns).length = source.length := by simp [code]

theorem lookup (source : Code) (target : Nat) (returns : Nat → Bool) (pc : Nat) :
    (code source target returns)[pc]? = (source[pc]?).map (instruction target returns pc) := by
  simp [code]

theorem nonhalt (target : Nat) (returns : Nat → Bool) (pc : Nat) (op : Instruction)
    (hne : op ≠ .native .halt) : instruction target returns pc op = op := by
  unfold instruction
  split
  · cases op with
    | call => rfl
    | native native => simp [HaltReturn.instruction, show native ≠ .halt from by simpa using hne]
  · rfl

theorem active_eval (source : Code) (target : Nat) (returns : Nat → Bool)
    (oracle : BitOracle State) (fuel : Nat) (start : Configuration State)
    (active : ∀ out ∈ (TimedExecution.eval (Reification.timedStep source oracle) fuel start).support,
      Reification.terminal out.control = false) :
    TimedExecution.eval (Reification.timedStep (code source target returns) oracle) fuel start =
      TimedExecution.eval (Reification.timedStep source oracle) fuel start := by
  apply HaltReturn.active_eval_of_fetch source (code source target returns) _ oracle fuel start active
  intro pc op hf hn
  rw [lookup, hf, Option.map_some, nonhalt _ _ _ _ hn]

theorem return_run (source : Code) (target : Nat) (returns : Nat → Bool)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (start before : Machine.Configuration) (fuel : Nat) (ha : before.halted = false)
    (hp : TimedExecution.eval (Reification.timedStep source oracle) fuel (NativeCode.frame state trace start) =
      PMF.pure (NativeCode.frame state trace before))
    (hh : source[before.pc]? = some (.native .halt)) (hr : returns before.pc = true) :
    TimedExecution.eval (Reification.timedStep (code source target returns) oracle) (fuel + 1)
      (NativeCode.frame state trace start) =
      PMF.pure (NativeCode.frame state trace (before.resumeAt target)) := by
  have unchanged := active_eval source target returns oracle fuel (NativeCode.frame state trace start)
    (by intro out hm; rw [hp, PMF.mem_support_pure_iff] at hm; subst out; exact ha)
  have fetched := lookup source target returns before.pc
  rw [hh] at fetched
  simp only [Option.map_some, instruction, hr, ↓reduceIte, HaltReturn.instruction, ↓reduceIte] at fetched
  rw [TimedExecution.eval_add, unchanged, hp, PMF.pure_bind]
  simp [TimedExecution.eval, Reification.timedStep, Reification.terminal, NativeCode.frame,
    Reification.perform, Reification.action, transition, ha, fetched,
    Machine.Instruction.next, Machine.Configuration.resumeAt]

theorem halt_run (source : Code) (target : Nat) (returns : Nat → Bool)
    (oracle : BitOracle State) (state : State) (trace : List (List Bool × List Bool))
    (start before : Machine.Configuration) (fuel : Nat) (ha : before.halted = false)
    (hp : TimedExecution.eval (Reification.timedStep source oracle) fuel (NativeCode.frame state trace start) =
      PMF.pure (NativeCode.frame state trace before))
    (hh : source[before.pc]? = some (.native .halt)) (hr : returns before.pc = false) :
    TimedExecution.eval (Reification.timedStep (code source target returns) oracle) (fuel + 1)
      (NativeCode.frame state trace start) =
      PMF.pure (NativeCode.frame state trace { before with halted := true }) := by
  have unchanged := active_eval source target returns oracle fuel (NativeCode.frame state trace start)
    (by intro out hm; rw [hp, PMF.mem_support_pure_iff] at hm; subst out; exact ha)
  have fetched := lookup source target returns before.pc
  rw [hh] at fetched
  simp only [Option.map_some, instruction, hr, Bool.false_eq_true, ↓reduceIte] at fetched
  rw [TimedExecution.eval_add, unchanged, hp, PMF.pure_bind]
  simp [TimedExecution.eval, Reification.timedStep, Reification.terminal, NativeCode.frame,
    Reification.perform, Reification.action, transition, ha, fetched, Machine.Instruction.next]

theorem code_native (source : Code) (target : Nat) (returns : Nat → Bool)
    (hs : ∀ op ∈ source, ∃ native, op = .native native) :
    ∀ op ∈ code source target returns, ∃ native, op = .native native := by
  intro op member
  obtain ⟨pc, inside, he⟩ := List.exists_of_mem_mapIdx member
  obtain ⟨native, hn⟩ := hs source[pc] (List.getElem_mem inside)
  rw [← he, hn]
  unfold instruction
  split <;> exact ⟨_, rfl⟩

end CryptoOracle.Interactive.SelectiveHaltReturn
