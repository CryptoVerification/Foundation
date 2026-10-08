import Foundation.Crypto.Semantics.Oracle.AdaptiveBitstringLoop
import Foundation.Crypto.Semantics.Asymptotic.PolynomiallyBounded

/-! Complete execution of the fixed five-command adaptive bitstring caller.
The response support cap bounds every actual loader. The initial request may
have a different length. Every next request is the preceding physical reply;
no oracle reply is precomputed and no round exit is freely canonicalized. -/
namespace CryptoOracle.Interactive.AdaptiveBitstringLoop
open Machine Foundation.Probability TimedExecution
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def finished {State : Type u} (state : State) (past : List (Option Bool)) (request : List Bool)
    (trace : List (List Bool × List Bool)) : Configuration State :=
  ⟨state, .running { machine 0 past request with pc := 4, halted := true }, trace⟩

def timeBound (cap rounds requestSize : Nat) : Nat := rounds * (5 * cap + 9) + 2 * requestSize + 2

noncomputable def law {State : Type u} (oracle : BitOracle State) :
    Nat → State → List (Option Bool) → List Bool → List (List Bool × List Bool) → PMF (Configuration State)
  | 0, state, past, request, trace => PMF.pure (finished state past request trace)
  | rounds + 1, state, past, request, trace => (oracle state request).bind fun answer =>
      law oracle rounds answer.1 (some true :: past) answer.2 ((request, answer.2) :: trace)

variable {State : Type u} (oracle : BitOracle State)

noncomputable def finish (state : State) (past : List (Option Bool)) (request : List Bool)
    (trace : List (List Bool × List Bool)) : Procedure (Reification.timedStep code oracle) Unit (Configuration State) :=
  Procedure.ofFixed (Reification.timedStep code oracle) (fun _ => frame state 0 past request trace)
    (fun _ result => result) (fun _ => PMF.pure (finished state past request trace)) (fun _ => 2) (fun _ => by
      cases request <;> simp [TimedExecution.eval, finished, frame, machine, ResponseLoading.loaded,
        ResponseLoading.fromCells, Reification.timedStep, Reification.terminal, Reification.perform,
        Reification.action, transition, code, Machine.Instruction.next, Machine.Configuration.tape,
        Machine.Configuration.advance, Tape.ofBits, PMF.pure_map])

structure Run (cap rounds : Nat) (state : State) (past : List (Option Bool)) (request : List Bool)
    (trace : List (List Bool × List Bool)) where
  execution : Procedure (Reification.timedStep code oracle) Unit (Configuration State)
  entry_eq : execution.entry () = frame state rounds past request trace
  exit_eq : ∀ output, execution.exit () output = output
  budget_eq : execution.budget () = timeBound cap rounds request.length
  semantics_eq : execution.semantics () = law oracle rounds state past request trace

variable (cap : Nat)
    (hResponse : ∀ state request answer, answer ∈ (oracle state request).support → answer.2.length ≤ cap)

noncomputable def whole : (rounds : Nat) → (state : State) → (past : List (Option Bool)) →
    (request : List Bool) → (trace : List (List Bool × List Bool)) → Run oracle cap rounds state past request trace
  | 0, state, past, request, trace =>
      ⟨(finish oracle state past request trace).withBudget (fun _ => timeBound cap 0 request.length)
        (fun _ => by change 2 ≤ timeBound cap 0 request.length; unfold timeBound; omega),
        rfl, (fun _ => rfl), rfl, rfl⟩
  | rounds + 1, state, past, request, trace =>
      let next := fun answer : State × List Bool =>
        whole rounds answer.1 (some true :: past) answer.2 ((request, answer.2) :: trace)
      let first := round oracle state rounds past request trace cap hResponse
      let second := Procedure.dispatch (fun answer => (next answer).execution)
      let both := first.seq second
        (fun _ answer _ => (next answer).entry_eq)
        (fun _ => timeBound cap rounds cap) (by
          intro input answer hs
          cases input
          change answer ∈ (first.semantics ()).support at hs
          rw [round_semantics] at hs
          change (next answer).execution.budget () ≤ _
          rw [(next answer).budget_eq]
          have hLength := hResponse state request answer hs
          unfold timeBound
          omega)
      let result := both.observe Prod.snd (fun _ output => output)
        (by intro input output _; cases input; exact ((next output.1).exit_eq output.2).symm)
      ⟨result, rfl, (fun _ => rfl), (by
        change first.budget () + timeBound cap rounds cap = _
        rw [round_budget]
        unfold timeBound
        simp only [Nat.add_mul, Nat.one_mul]
        omega), (by
        change ((first.semantics ()).bind (fun answer =>
          ((next answer).execution.semantics ()).map (fun output => (answer, output)))).map Prod.snd = _
        rw [round_semantics, PMF.map_bind]
        change (oracle state request).bind _ = (oracle state request).bind _
        congr 1
        funext answer
        rw [PMF.map_comp]
        change ((next answer).execution.semantics ()).map id = _
        rw [PMF.map_id, (next answer).semantics_eq])⟩

theorem law_support (rounds : Nat) (state : State) (past : List (Option Bool)) (request : List Bool)
    (trace : List (List Bool × List Bool)) (result : Configuration State)
    (h : result ∈ (law oracle rounds state past request trace).support) :
    Reification.terminal result.control = true ∧ result.reverseTrace.length = rounds + trace.length := by
  induction rounds generalizing state past request trace result with
  | zero =>
      rw [law, PMF.mem_support_pure_iff] at h
      subst result
      exact ⟨rfl, by simp [finished]⟩
  | succ rounds ih =>
      rw [law, PMF.mem_support_bind_iff] at h
      obtain ⟨answer, _, h⟩ := h
      have hr := ih answer.1 (some true :: past) answer.2 ((request, answer.2) :: trace) result h
      exact ⟨hr.1, by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr.2⟩

include hResponse in
theorem run (rounds : Nat) (state : State) (past : List (Option Bool)) (request : List Bool)
    (trace : List (List Bool × List Bool)) (horizon : Nat) (hTime : timeBound cap rounds request.length ≤ horizon) :
    TimedExecution.eval (Reification.timedStep code oracle) horizon (frame state rounds past request trace) =
      law oracle rounds state past request trace := by
  let C := whole oracle cap hResponse rounds state past request trace
  have h := C.execution.final_run () (fun output hs => by
    rw [C.exit_eq]
    have hComplete := (law_support oracle rounds state past request trace output (by rw [← C.semantics_eq]; exact hs)).1
    simp [Reification.timedStep, hComplete]) horizon (by rw [C.budget_eq]; exact hTime)
  have hExit : C.execution.exit () = id := funext C.exit_eq
  rw [C.entry_eq, C.semantics_eq, hExit, PMF.map_id] at h
  exact h

include hResponse in
theorem halts_and_queries (rounds : Nat) (state : State) (past : List (Option Bool)) (request : List Bool)
    (trace : List (List Bool × List Bool)) (horizon : Nat) (hTime : timeBound cap rounds request.length ≤ horizon)
    (result : Configuration State)
    (h : result ∈ (TimedExecution.eval (Reification.timedStep code oracle) horizon
      (frame state rounds past request trace)).support) :
    Reification.terminal result.control = true ∧ result.reverseTrace.length = rounds + trace.length := by
  rw [run oracle cap hResponse rounds state past request trace horizon hTime] at h
  exact law_support oracle rounds state past request trace result h

theorem time_polynomial {cap rounds requestSize : Nat → Nat}
    (hCap : PolynomiallyBounded cap) (hRounds : PolynomiallyBounded rounds)
    (hRequest : PolynomiallyBounded requestSize) : PolynomiallyBounded (fun n => timeBound (cap n) (rounds n) (requestSize n)) :=
  ((hRounds.mul (((PolynomiallyBounded.const 5).mul hCap).add (PolynomiallyBounded.const 9))).add
    ((PolynomiallyBounded.const 2).mul hRequest)).add (PolynomiallyBounded.const 2)

end CryptoOracle.Interactive.AdaptiveBitstringLoop
