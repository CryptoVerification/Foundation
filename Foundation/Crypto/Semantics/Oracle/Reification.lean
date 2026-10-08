import Foundation.Crypto.Semantics.Oracle.InteractiveMachine
import Foundation.Crypto.Semantics.Oracle.ResultMap

/-! A finite interactive code has a bounded adaptive oracle-program semantics.
Reification is analysis, not code generation: it may expand a decision tree.
The source machine retains its real transition budget. Reification observes
only the public controller, never the oracle's private state or transcript. -/
namespace CryptoOracle.Interactive.Reification
open Foundation.Probability
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-- Stop immediately after the native halt, retaining its output packet.
The old finished-bit controller is also terminal. -/
def terminal : Control → Bool
  | .running machine => machine.halted
  | .finished _ => true
  | _ => false

def action (code : Code) (control : Control) : Transition Unit :=
  transition code ⟨(), control, []⟩

noncomputable def perform {State : Type u} (code : Code) (oracle : BitOracle State)
    (c : Configuration State) : PMF (Configuration State) :=
  match action code c.control with
  | .deterministic next => PMF.pure { c with control := next.control }
  | .random zero one => sampleBit.map fun bit =>
      { c with control := if bit then one.control else zero.control }
  | .oracleCall machine request => (oracle c.state request).map fun response =>
      { state := response.1, control := .loading machine response.2 {},
        reverseTrace := (request, response.2) :: c.reverseTrace }

/-- The instruction choice depends only on controller data; private oracle
state is used exclusively when the machine explicitly issues a query. -/
theorem step_eq_perform {State : Type u} (code : Code) (oracle : BitOracle State)
    (c : Configuration State) : step code oracle c = perform code oracle c := by
  rcases c with ⟨state, control, trace⟩
  cases control with
  | running machine =>
      cases hh : machine.halted with
      | true => simp [step, perform, action, transition, hh]
      | false =>
          cases hi : code[machine.pc]? with
          | none => simp [step, perform, action, transition, hh, hi]
          | some instruction =>
              cases instruction with
              | call => simp [step, perform, action, transition, hh, hi]
              | native instruction =>
                  cases hn : instruction.next machine with
                  | inl next => simp [step, perform, action, transition, hh, hi, hn]
                  | inr pair =>
                      simp [step, perform, action, transition, hh, hi, hn]
                      congr 1
                      funext bit
                      cases bit <;> rfl
  | sending machine tape reversed =>
      cases ht : tape.current <;> simp [step, perform, action, transition, ht]
  | reversing machine remaining request =>
      cases remaining <;> simp [step, perform, action, transition]
  | awaiting machine request => simp [step, perform, action, transition]
  | loading machine remaining tape =>
      cases remaining <;> simp [step, perform, action, transition]
  | advancing machine remaining tape => simp [step, perform, action, transition]
  | rewinding machine tape =>
      cases hl : tape.left <;> simp [step, perform, action, transition, hl]
  | finished result => simp [step, perform, action, transition]

/-- Bounded execution stops at the actual native halt and preserves the
whole output packet. Unfinished executions retain their unfinished control. -/
noncomputable def eval {State : Type u} (code : Code) (oracle : BitOracle State) :
    Nat → Configuration State → PMF (Configuration State)
  | fuel, c => if terminal c.control then PMF.pure c else match fuel with
    | 0 => PMF.pure c
    | fuel + 1 => (step code oracle c).bind (eval code oracle fuel)

/-- The finite adaptive program contains explicit local coins and explicit
queries, while deterministic native transitions are evaluated locally. -/
def program (code : Code) : Nat → Control → CryptoOracle.Program (List Bool) (List Bool) Control
  | fuel, control => if terminal control then .done control else match fuel with
    | 0 => .done control
    | fuel + 1 => match action code control with
      | .deterministic next => program code fuel next.control
      | .random zero one => .coin (fun bit => program code fuel (if bit then one.control else zero.control))
      | .oracleCall machine request => .query request
          (fun response => program code fuel (.loading machine response {}))

/-- Restore the machine's initial transcript prefix as well as the final
oracle state. No private oracle state is supplied to the reified program. -/
def assemble {State : Type u} (prior : List (List Bool × List Bool))
    (out : CryptoOracle.Outcome (List Bool) (List Bool) Control State) : Configuration State :=
  ⟨out.state, out.result, out.trace.reverse ++ prior⟩

/-- Exact joint distribution of control, oracle state, and entire transcript. -/
theorem program_run {State : Type u} (code : Code) (oracle : BitOracle State)
    (fuel : Nat) (c : Configuration State) :
    ((program code fuel c.control).run oracle c.state).map (assemble c.reverseTrace) =
      eval code oracle fuel c := by
  induction fuel generalizing c with
  | zero =>
      simp [program, eval, CryptoOracle.Program.run, assemble, PMF.pure_map]
  | succ fuel ih =>
      by_cases h : terminal c.control = true
      · simp [program, eval, h, CryptoOracle.Program.run, assemble, PMF.pure_map]
      · simp only [program, eval, h, Bool.false_eq_true, if_false, step_eq_perform, perform]
        cases ha : action code c.control with
        | deterministic next =>
            simp only [ha, PMF.pure_bind]
            exact ih { c with control := next.control }
        | random zero one =>
            simp only [ha, CryptoOracle.Program.run, PMF.map_bind, PMF.bind_map, Function.comp_def]
            congr 1
            funext bit
            exact ih { c with control := if bit then one.control else zero.control }
        | oracleCall machine request =>
            simp only [ha, CryptoOracle.Program.run, PMF.map_bind, PMF.bind_map, Function.comp_def]
            congr 1
            funext response
            rw [← ih ⟨response.1, .loading machine response.2 {}, (request, response.2) :: c.reverseTrace⟩]
            simp only [PMF.map_comp, Function.comp_def]
            congr 1
            funext out
            simp [assemble, List.reverse_cons, List.append_assoc]

/-- There is at most one external query per actual machine transition.
Transfers and local native computation keep their separate fuel charges. -/
theorem program_queries (code : Code) (fuel : Nat) (control : Control) :
    (program code fuel control).BoundedQueries fuel := by
  induction fuel generalizing control with
  | zero =>
      simp only [program]
      split <;> exact .done _ _
  | succ fuel ih =>
      simp only [program]
      split
      · exact .done _ _
      · cases action code control with
        | deterministic next => exact (ih next.control).mono (Nat.le_succ fuel)
        | random zero one =>
            exact .coin _ _ (fun bit => (ih _).mono (Nat.le_succ fuel))
        | oracleCall machine request => exact .query _ _ fuel (fun response => ih _)

theorem eval_zero {State : Type u} (code : Code) (oracle : BitOracle State) (c : Configuration State) :
    eval code oracle 0 c = PMF.pure c := by simp [eval]

theorem eval_terminal {State : Type u} (code : Code) (oracle : BitOracle State)
    (fuel : Nat) (c : Configuration State) (h : terminal c.control = true) :
    eval code oracle fuel c = PMF.pure c := by cases fuel <;> simp [eval, h]

/-- Splitting a real execution budget does not reset tapes or oracle state. -/
theorem eval_add {State : Type u} (code : Code) (oracle : BitOracle State)
    (first second : Nat) (c : Configuration State) :
    eval code oracle (first + second) c =
      (eval code oracle first c).bind (eval code oracle second) := by
  induction first generalizing c with
  | zero => simp [eval_zero]
  | succ first ih =>
      by_cases h : terminal c.control = true
      · simp [eval_terminal _ _ _ _ h]
      · have ht : terminal c.control = false := Bool.eq_false_iff.mpr h
        have hs (n : Nat) : eval code oracle (n + 1) c =
            (step code oracle c).bind (eval code oracle n) := by simp [eval, ht]
        rw [Nat.succ_add, hs, hs, PMF.bind_bind]
        congr 1
        funext next
        exact ih next

/-- Completion checks real controller termination; fuel exhaustion alone
cannot manufacture a halting or resource certificate. -/
def HaltsWithin {State : Type u} (code : Code) (oracle : BitOracle State)
    (start : Configuration State) (fuel : Nat) : Prop :=
  ∀ finish ∈ (eval code oracle fuel start).support, terminal finish.control = true

/-- The semantic program retains the machine's genuine halting obligation. -/
theorem program_terminates {State : Type u} (code : Code) (oracle : BitOracle State)
    (fuel : Nat) (start : Configuration State) (h : HaltsWithin code oracle start fuel)
    (out : CryptoOracle.Outcome (List Bool) (List Bool) Control State)
    (hout : out ∈ ((program code fuel start.control).run oracle start.state).support) :
    terminal out.result = true := by
  have hm : assemble start.reverseTrace out ∈
      (((program code fuel start.control).run oracle start.state).map (assemble start.reverseTrace)).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨out, hout, rfl⟩
  rw [program_run] at hm
  exact h _ hm

/-- A genuine stopping certificate makes larger budgets observationally
identical, including the complete output tape and transcript. -/
theorem eval_stable {State : Type u} (code : Code) (oracle : BitOracle State)
    (fuel extra : Nat) (start : Configuration State) (h : HaltsWithin code oracle start fuel) :
    eval code oracle (fuel + extra) start = eval code oracle fuel start := by
  rw [eval_add, ← PMF.bindOnSupport_eq_bind]
  calc
    _ = (eval code oracle fuel start).bindOnSupport (fun c _ => PMF.pure c) := by
      congr 1
      funext c hc
      exact eval_terminal code oracle extra c (h c hc)
    _ = _ := PMF.bindOnSupport_pure _

/-- Native output packets are observed at the halt without replacing them
by the old single finished bit. An unfinished controller yields no packet. -/
def packet : Control → Option (List Bool)
  | .running machine => if machine.halted then some machine.outputBits else none
  | .finished bit => some [bit]
  | _ => none

def observe {Result : Type*} {State : Type u} (decode : Control → Result)
    (c : Configuration State) : CryptoOracle.Outcome (List Bool) (List Bool) Result State :=
  ⟨decode c.control, c.state, c.reverseTrace.reverse⟩

/-- Result observation is a semantic boundary. An arbitrary decoder does
not acquire a CPU certificate from this equality. The packet observer below
only exposes the native machine's actual output bits. -/
theorem decoded_program_run {Result : Type*} {State : Type u} (decode : Control → Result)
    (code : Code) (oracle : BitOracle State) (fuel : Nat) (control : Control) (state : State) :
    ((program code fuel control).mapResult decode).run oracle state =
      (eval code oracle fuel ⟨state, control, []⟩).map (observe decode) := by
  rw [← program_run code oracle fuel ⟨state, control, []⟩]
  simp [CryptoOracle.Program.mapResult_run, PMF.map_comp, Function.comp_def,
    assemble, observe, CryptoOracle.Program.decodeOutcome]
  rfl

def packetProgram (code : Code) (fuel : Nat) (control : Control) :
    CryptoOracle.Program (List Bool) (List Bool) (Option (List Bool)) :=
  (program code fuel control).mapResult packet

theorem packet_program_run {State : Type u} (code : Code) (oracle : BitOracle State)
    (fuel : Nat) (control : Control) (state : State) :
    (packetProgram code fuel control).run oracle state =
      (eval code oracle fuel ⟨state, control, []⟩).map (observe packet) :=
  decoded_program_run packet code oracle fuel control state

theorem packet_program_queries (code : Code) (fuel : Nat) (control : Control) :
    (packetProgram code fuel control).BoundedQueries fuel :=
  CryptoOracle.Program.mapResult_queries packet (program_queries code fuel control)

theorem terminal_packet (control : Control) (h : terminal control = true) :
    (packet control).isSome = true := by
  cases control <;> simp_all [terminal, packet]

/-- Executable packet simulator; stopping and every charged transition use
exactly the controller and native transition functions of the PMF semantics. -/
def simulate {State : Type u} (code : Code) (oracle : State → List Bool → State × List Bool)
    (coin : Bool) : Nat → Configuration State → Configuration State × Nat
  | fuel, c => if terminal c.control then (c, 0) else match fuel with
    | 0 => (c, 0)
    | fuel + 1 =>
        let result := simulate code oracle coin fuel (simulateStep code oracle coin c)
        (result.1, result.2 + 1)

theorem simulate_steps_le {State : Type u} (code : Code)
    (oracle : State → List Bool → State × List Bool) (coin : Bool) (fuel : Nat) (c : Configuration State) :
    (simulate code oracle coin fuel c).2 ≤ fuel := by
  induction fuel generalizing c with
  | zero => simp [simulate]
  | succ fuel ih =>
      by_cases h : terminal c.control = true
      · simp [simulate, h]
      · simpa [simulate, h] using Nat.succ_le_succ (ih (simulateStep code oracle coin c))

/-- Each concrete simulated path is a supported path of the same execution
semantics, including its full packet, oracle state, and query history. -/
theorem simulate_mem_support {State : Type u} (code : Code)
    (oracle : State → List Bool → State × List Bool) (coin : Bool) (fuel : Nat) (c : Configuration State) :
    (simulate code oracle coin fuel c).1 ∈
      (eval code (fun state request => PMF.pure (oracle state request)) fuel c).support := by
  induction fuel generalizing c with
  | zero => simp [simulate, eval]
  | succ fuel ih =>
      by_cases h : terminal c.control = true
      · simp [simulate, eval, h]
      · simp only [simulate, eval, h, Bool.false_eq_true, if_false, PMF.mem_support_bind_iff]
        exact ⟨simulateStep code oracle coin c, simulateStep_mem_support code oracle coin c,
          ih (simulateStep code oracle coin c)⟩

end CryptoOracle.Interactive.Reification
