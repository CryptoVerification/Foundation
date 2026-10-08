import Foundation.Crypto.Semantics.Oracle.FreshMaskAdaptiveRound
import Foundation.Crypto.Semantics.Oracle.AdaptiveBitstringLoopExecution

/-! The fixed adaptive caller repeatedly executes actual native fresh-key
masking, including all request/response transfers, then genuinely halts.
Each ciphertext becomes the next physical request. All supported branches
retain the complete caller, transcript and consumed counter cells. -/
namespace CryptoOracle.Interactive.FreshMaskAdaptiveExecution
open Machine Foundation.Probability TimedExecution Foundation.Symmetric
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def timeBound (rounds width : Nat) : Nat := rounds * (72 * width + 58) + 2

noncomputable def law {State : Type u} : Nat → State → List (Option Bool) → List Bool →
    List (List Bool × List Bool) → PMF (Configuration State)
  | 0, state, past, request, trace => PMF.pure (AdaptiveBitstringLoop.finished state past request trace)
  | rounds + 1, state, past, request, trace => (uniform (Bits request.length)).bind fun ciphertext =>
      law rounds state (some true :: past) ciphertext.toList ((request, ciphertext.toList) :: trace)

variable {State : Type u} (oracle : BitOracle State)

noncomputable def finish (state : State) (past : List (Option Bool)) (request : List Bool)
    (trace : List (List Bool × List Bool)) :
    TimedExecution.Procedure (FreshMaskAdaptiveRound.runtime oracle).step Unit (Configuration State) :=
  TimedExecution.Procedure.ofFixed _
    (fun _ => (FreshMaskAdaptiveRound.runtime oracle).embed () (AdaptiveBitstringLoop.frame state 0 past request trace))
    (fun _ result => (FreshMaskAdaptiveRound.runtime oracle).embed () result)
    (fun _ => PMF.pure (AdaptiveBitstringLoop.finished state past request trace)) (fun _ => 2)
    (fun _ => by
      cases request <;> simp [TimedExecution.eval, FreshMaskAdaptiveRound.runtime, CallerRuntime.packet,
        PacketResponseSource.step, AdaptiveBitstringLoop.finished, AdaptiveBitstringLoop.frame,
        AdaptiveBitstringLoop.machine, ResponseLoading.loaded, ResponseLoading.fromCells,
        Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition,
        AdaptiveBitstringLoop.code, Machine.Instruction.next, Machine.Configuration.tape,
        Machine.Configuration.advance, Tape.ofBits, PMF.pure_map])

structure Run (rounds : Nat) (state : State) (past : List (Option Bool)) (request : List Bool)
    (trace : List (List Bool × List Bool)) where
  execution : TimedExecution.Procedure (FreshMaskAdaptiveRound.runtime oracle).step Unit (Configuration State)
  entry_eq : execution.entry () = (FreshMaskAdaptiveRound.runtime oracle).embed ()
    (AdaptiveBitstringLoop.frame state rounds past request trace)
  exit_eq : ∀ output, execution.exit () output = (FreshMaskAdaptiveRound.runtime oracle).embed () output
  budget_eq : execution.budget () = timeBound rounds request.length
  semantics_eq : execution.semantics () = law rounds state past request trace

noncomputable def whole : (rounds : Nat) → (state : State) → (past : List (Option Bool)) →
    (request : List Bool) → (trace : List (List Bool × List Bool)) → Run oracle rounds state past request trace
  | 0, state, past, request, trace =>
      ⟨finish oracle state past request trace, rfl, fun _ => rfl,
        (by change 2 = timeBound 0 request.length; simp [timeBound]), rfl⟩
  | rounds + 1, state, past, request, trace =>
      let next := fun packet : List Bool => whole rounds state (some true :: past) packet ((request, packet) :: trace)
      let first := FreshMaskAdaptiveRound.round oracle state rounds past request trace
      let second := TimedExecution.Procedure.dispatch (fun packet => (next packet).execution)
      let both := first.seq second
        (fun _ packet _ => (next packet).entry_eq)
        (fun _ => timeBound rounds request.length) (by
          intro input packet hs
          cases input
          change packet ∈ (first.semantics ()).support at hs
          rw [FreshMaskAdaptiveRound.round_semantics, PMF.mem_support_map_iff] at hs
          obtain ⟨ciphertext, _, rfl⟩ := hs
          change (next ciphertext.toList).execution.budget () ≤ _
          rw [(next ciphertext.toList).budget_eq, Bits.length_toList])
      let result := both.observe Prod.snd
        (fun _ output => (FreshMaskAdaptiveRound.runtime oracle).embed () output)
        (by intro input output _; cases input; exact ((next output.1).exit_eq output.2).symm)
      ⟨result, rfl, (fun _ => rfl), (by
        change first.budget () + timeBound rounds request.length = _
        rw [FreshMaskAdaptiveRound.round_budget]
        unfold timeBound
        simp only [Nat.add_mul, Nat.one_mul]
        omega), (by
        change ((first.semantics ()).bind (fun packet =>
          ((next packet).execution.semantics ()).map (fun output => (packet, output)))).map Prod.snd = _
        rw [FreshMaskAdaptiveRound.round_semantics, PMF.map_bind, PMF.bind_map]
        change (uniform (Bits request.length)).bind _ = (uniform (Bits request.length)).bind _
        congr 1
        funext ciphertext
        dsimp only [Function.comp_def]
        rw [PMF.map_comp]
        change ((next ciphertext.toList).execution.semantics ()).map id = _
        rw [PMF.map_id, (next ciphertext.toList).semantics_eq])⟩

theorem law_support (rounds : Nat) (state : State) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) (final : Configuration State)
    (hFinal : final ∈ (law rounds state past request trace).support) :
    Reification.terminal final.control = true ∧ final.reverseTrace.length = trace.length + rounds := by
  induction rounds generalizing past request trace with
  | zero =>
      rw [law, PMF.mem_support_pure_iff] at hFinal
      subst final
      simp [AdaptiveBitstringLoop.finished, Reification.terminal]
  | succ rounds ih =>
      rw [law, PMF.mem_support_bind_iff] at hFinal
      obtain ⟨ciphertext, _, hFinal⟩ := hFinal
      obtain ⟨ht, hl⟩ := ih (some true :: past) ciphertext.toList ((request, ciphertext.toList) :: trace) hFinal
      exact ⟨ht, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hl⟩

/-- No external reply law is used to compute the ciphertext. The registered
component performs its own native randomness and encryption on every call. -/
theorem run (rounds : Nat) (state : State) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) (horizon : Nat)
    (hTime : timeBound rounds request.length ≤ horizon) :
    TimedExecution.eval (FreshMaskAdaptiveRound.runtime oracle).step horizon
      ((FreshMaskAdaptiveRound.runtime oracle).embed () (AdaptiveBitstringLoop.frame state rounds past request trace)) =
      (law rounds state past request trace).map ((FreshMaskAdaptiveRound.runtime oracle).embed ()) := by
  let all := whole oracle rounds state past request trace
  have h := all.execution.final_run () (fun final hs => by
    rw [all.exit_eq]
    apply (FreshMaskAdaptiveRound.runtime oracle).terminal
    have hl := all.semantics_eq
    rw [hl] at hs
    exact (law_support rounds state past request trace final hs).1)
    horizon (by rw [all.budget_eq]; exact hTime)
  rw [all.entry_eq, all.semantics_eq] at h
  have hExit : all.execution.exit () = (FreshMaskAdaptiveRound.runtime oracle).embed () := funext all.exit_eq
  rw [hExit] at h
  exact h

theorem halts_and_queries (rounds : Nat) (state : State) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) (horizon : Nat)
    (hTime : timeBound rounds request.length ≤ horizon) (final : PacketResponseSource.Control NativePacketService.Control State Unit)
    (hFinal : final ∈ (TimedExecution.eval (FreshMaskAdaptiveRound.runtime oracle).step horizon
      ((FreshMaskAdaptiveRound.runtime oracle).embed () (AdaptiveBitstringLoop.frame state rounds past request trace))).support) :
    ∃ frame, final = (FreshMaskAdaptiveRound.runtime oracle).embed () frame ∧
      Reification.terminal frame.control = true ∧ frame.reverseTrace.length = trace.length + rounds := by
  rw [run oracle rounds state past request trace horizon hTime, PMF.mem_support_map_iff] at hFinal
  obtain ⟨frame, hs, he⟩ := hFinal
  exact ⟨frame, he.symm, law_support rounds state past request trace frame hs⟩

/-- Ciphertexts are generated by the native component, independently of
any unused external response law supplied to the source evaluator. -/
theorem external_independence (other : BitOracle State) (rounds : Nat) (state : State)
    (past : List (Option Bool)) (request : List Bool) (trace : List (List Bool × List Bool))
    (horizon : Nat) (hTime : timeBound rounds request.length ≤ horizon) :
    TimedExecution.eval (FreshMaskAdaptiveRound.runtime oracle).step horizon
      ((FreshMaskAdaptiveRound.runtime oracle).embed () (AdaptiveBitstringLoop.frame state rounds past request trace)) =
    TimedExecution.eval (FreshMaskAdaptiveRound.runtime other).step horizon
      ((FreshMaskAdaptiveRound.runtime other).embed () (AdaptiveBitstringLoop.frame state rounds past request trace)) := by
  rw [run oracle rounds state past request trace horizon hTime,
    run other rounds state past request trace horizon hTime]
  rfl

theorem time_polynomial {rounds width : Nat → Nat}
    (hRounds : PolynomiallyBounded rounds) (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n => timeBound (rounds n) (width n)) :=
  (hRounds.mul (((PolynomiallyBounded.const 72).mul hWidth).add
    (PolynomiallyBounded.const 58))).add (PolynomiallyBounded.const 2)

end CryptoOracle.Interactive.FreshMaskAdaptiveExecution
