import Foundation.Crypto.Semantics.Oracle.Program
import Foundation.Crypto.Semantics.Machine.Execution

/-! A finite oracle machine. Native instructions are the existing bit-machine
instructions. A call reads a contiguous request from the current output head,
transfers it cell by cell, loads the response cell by cell, rewinds, and resumes
the same code with its input/work tape intact. Oracle evaluation is a capability
costing one step; its internal computation belongs to the experiment.
The transcript is an observation, never an input available to native code. -/

namespace CryptoOracle.Interactive

open Foundation.Probability

universe u

inductive Instruction where
  | native : Machine.Instruction → Instruction
  | call : Instruction
  deriving DecidableEq, Repr, Encodable

abbrev Code := List Instruction

inductive Control where
  | running : Machine.Configuration → Control
  | sending : Machine.Configuration → Machine.Tape → List Bool → Control
  | reversing : Machine.Configuration → List Bool → List Bool → Control
  | awaiting : Machine.Configuration → List Bool → Control
  | loading : Machine.Configuration → List Bool → Machine.Tape → Control
  | advancing : Machine.Configuration → List Bool → Machine.Tape → Control
  | rewinding : Machine.Configuration → Machine.Tape → Control
  | finished : Bool → Control
  deriving DecidableEq, Repr

structure Configuration (State : Type u) where
  state : State
  control : Control
  reverseTrace : List (List Bool × List Bool) := []

namespace Configuration

def initial {State : Type u} (state : State) (input : List Bool) : Configuration State :=
  ⟨state, .running (Machine.Configuration.initial input), []⟩

def complete {State : Type u} (c : Configuration State) : Prop :=
  ∃ result, c.control = .finished result

def result {State : Type u} (c : Configuration State) : Option Bool :=
  match c.control with
  | .finished result => some result
  | _ => none

end Configuration

abbrev BitOracle (State : Type u) := Oracle (List Bool) (List Bool) State

inductive Transition (State : Type u) where
  | deterministic : Configuration State → Transition State
  | random : Configuration State → Configuration State → Transition State
  | oracleCall : Machine.Configuration → List Bool → Transition State

/-- One native instruction or one constant-size controller operation.
Buffer reversal, response writing, movement and rewinding are separate steps.
Finished states absorb padding, which is used only by the bounded evaluator. -/
def transition {State : Type u} (code : Code)
    (c : Configuration State) : Transition State :=
  match c.control with
  | .finished _ => .deterministic c
  | .running machine =>
      if machine.halted then
        .deterministic { c with control := .finished (machine.outputTape.current.getD false) }
      else
        match code[machine.pc]? with
        | none => .deterministic { c with control := .finished false }
        | some .call =>
            .deterministic { c with control := .sending machine.advance machine.outputTape [] }
        | some (.native instruction) =>
            match instruction.next machine with
            | .inl next => .deterministic { c with control := .running next }
            | .inr (zero, one) => .random { c with control := .running zero } { c with control := .running one }
  | .sending machine tape reversed =>
      match tape.current with
      | some bit => .deterministic { c with
          control := .sending machine tape.moveRight (bit :: reversed) }
      | none => .deterministic { c with control := .reversing machine reversed [] }
  | .reversing machine remaining request =>
      match remaining with
      | bit :: rest => .deterministic { c with control := .reversing machine rest (bit :: request) }
      | [] => .deterministic { c with control := .awaiting machine request }
  | .awaiting machine request =>
      .oracleCall machine request
  | .loading machine remaining tape =>
      match remaining with
      | bit :: rest => .deterministic { c with
          control := .advancing machine rest (tape.write (some bit)) }
      | [] => .deterministic { c with control := .rewinding machine tape }
  | .advancing machine remaining tape =>
      .deterministic { c with control := .loading machine remaining tape.moveRight }
  | .rewinding machine tape =>
      match tape.left with
      | [] => .deterministic { c with control := .running { machine with outputTape := tape } }
      | _ :: _ => .deterministic { c with control := .rewinding machine tape.moveLeft }

noncomputable def step {State : Type u} (code : Code) (oracle : BitOracle State)
    (c : Configuration State) : ProbComp (Configuration State) :=
  match transition code c with
  | .deterministic next => PMF.pure next
  | .random zero one => sampleBit.map fun bit => if bit then one else zero
  | .oracleCall machine request =>
      (oracle c.state request).map fun response =>
        { state := response.1, control := .loading machine response.2 {},
          reverseTrace := (request, response.2) :: c.reverseTrace }

/-- Executable path interpreter for a deterministic test oracle and explicit
coin choices. It uses exactly the transition function of the PMF semantics. -/
def simulateStep {State : Type u} (code : Code)
    (oracle : State → List Bool → State × List Bool) (coin : Bool)
    (c : Configuration State) : Configuration State :=
  match transition code c with
  | .deterministic next => next
  | .random zero one => if coin then one else zero
  | .oracleCall machine request =>
      let response := oracle c.state request
      { state := response.1, control := .loading machine response.2 {},
        reverseTrace := (request, response.2) :: c.reverseTrace }

/-- Returns the actual number of transitions until completion or fuel
exhaustion. Padding after completion is not charged by this interpreter. -/
def simulateLoop {State : Type u} (code : Code)
    (oracle : State → List Bool → State × List Bool) (coin : Bool) :
    Nat → Configuration State → Nat → Configuration State × Nat
  | 0, c, used => (c, used)
  | fuel + 1, c, used =>
      if c.result.isSome then (c, used) else
        simulateLoop code oracle coin fuel (simulateStep code oracle coin c) (used + 1)

def simulate {State : Type u} (code : Code)
    (oracle : State → List Bool → State × List Bool) (coin : Bool)
    (fuel : Nat) (c : Configuration State) : Configuration State × Nat :=
  simulateLoop code oracle coin fuel c 0

/-- Every executable test step is a possible step of the probabilistic
semantics for the same deterministic oracle, including either local coin. -/
theorem simulateStep_mem_support {State : Type u} (code : Code)
    (oracle : State → List Bool → State × List Bool) (coin : Bool)
    (c : Configuration State) :
    simulateStep code oracle coin c ∈
      (step code (fun state request => PMF.pure (oracle state request)) c).support := by
  cases h : transition code c with
  | deterministic next => simp [simulateStep, step, h]
  | random zero one =>
      simp only [simulateStep, step, h, PMF.mem_support_map_iff]
      exact ⟨coin, by simp [sampleBit, uniform], rfl⟩
  | oracleCall machine request => simp [simulateStep, step, h, PMF.pure_map]

noncomputable def eval {State : Type u} (code : Code) (oracle : BitOracle State)
    (start : Configuration State) : Nat → ProbComp (Configuration State)
  | 0 => PMF.pure start
  | fuel + 1 => (eval code oracle start fuel).bind (step code oracle)

/-- Genuine completion of every supported branch, rather than truncation at
the supplied fuel. A loop or an unfinished response transfer fails this test. -/
def HaltsWithin {State : Type u} (code : Code) (oracle : BitOracle State)
    (start : Configuration State) (fuel : Nat) : Prop :=
  ∀ finish ∈ (eval code oracle start fuel).support, finish.complete

theorem step_complete {State : Type u} (code : Code) (oracle : BitOracle State)
    (c : Configuration State) (h : c.complete) : step code oracle c = PMF.pure c := by
  obtain ⟨result, h⟩ := h
  simp [step, transition, h]

theorem eval_stable {State : Type u} (code : Code) (oracle : BitOracle State)
    (start : Configuration State) (fuel extra : Nat)
    (h : HaltsWithin code oracle start fuel) :
    eval code oracle start (fuel + extra) = eval code oracle start fuel := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ, eval, ih, ← PMF.bindOnSupport_eq_bind]
      calc
        (eval code oracle start fuel).bindOnSupport (fun c _ => step code oracle c) =
            (eval code oracle start fuel).bindOnSupport (fun c _ => PMF.pure c) := by
          congr 1
          funext c hc
          exact step_complete code oracle c (h c hc)
        _ = eval code oracle start fuel := PMF.bindOnSupport_pure _

theorem eval_eq_of_halts {State : Type u} (code : Code) (oracle : BitOracle State)
    (start : Configuration State) (fuel₁ fuel₂ : Nat)
    (h₁ : HaltsWithin code oracle start fuel₁) (h₂ : HaltsWithin code oracle start fuel₂) :
    eval code oracle start fuel₁ = eval code oracle start fuel₂ := by
  have hLeft := eval_stable code oracle start fuel₁ (max fuel₁ fuel₂ - fuel₁) h₁
  have hRight := eval_stable code oracle start fuel₂ (max fuel₁ fuel₂ - fuel₂) h₂
  rw [Nat.add_sub_of_le (le_max_left _ _)] at hLeft
  rw [Nat.add_sub_of_le (le_max_right _ _)] at hRight
  exact hLeft.symm.trans hRight

theorem HaltsWithin.mono {State : Type u} {code : Code} {oracle : BitOracle State}
    {start : Configuration State} {fuel fuel' : Nat}
    (h : HaltsWithin code oracle start fuel) (hle : fuel ≤ fuel') :
    HaltsWithin code oracle start fuel' := by
  have heq := eval_stable code oracle start fuel (fuel' - fuel) h
  rw [Nat.add_sub_of_le hle] at heq
  intro finish hFinish
  rw [heq] at hFinish
  exact h finish hFinish

/-- Observable traces are encoded protocol messages; private machine state
is omitted. `none` explicitly denotes an unfinished bounded execution. -/
structure Observation (State : Type u) where
  result : Option Bool
  state : State
  trace : List (List Bool × List Bool)

def observe {State : Type u} (c : Configuration State) : Observation State :=
  ⟨c.result, c.state, c.reverseTrace.reverse⟩

/-- Pure finite code construction; proof and resource data do not enter it. -/
inductive Compiler where
  | identity
  | suffix : Code → Compiler
  | constant : Code → Compiler
  | comp : Compiler → Compiler → Compiler
  deriving Repr, Encodable

def Compiler.run : Compiler → Code → Code
  | .identity, code => code
  | .suffix tail, code => code ++ tail
  | .constant target, _ => target
  | .comp first second, code => second.run (first.run code)

end CryptoOracle.Interactive
