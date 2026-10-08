import Foundation.Crypto.Semantics.Oracle.FreshMaskAdaptiveExecutionCosted
import Foundation.Crypto.Semantics.Oracle.PacketResponseTerminal
import Foundation.Crypto.Semantics.BoundaryExactTime

/-! The whole native adaptive execution has not halted one transition
before its complete horizon. Absorption excludes every earlier halt and
identifies the composed cumulative cost with the actual first halt. -/
namespace CryptoOracle.Interactive.FreshMaskAdaptiveExecution
open Machine Foundation.Probability TimedExecution Foundation.Symmetric
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

noncomputable def beforeHaltLaw {State : Type u} : Nat → State → List (Option Bool) → List Bool →
    List (List Bool × List Bool) → PMF (Configuration State)
  | 0, state, past, request, trace =>
      PMF.pure ⟨state, .running { AdaptiveBitstringLoop.machine 0 past request with pc := 4 }, trace⟩
  | rounds + 1, state, past, request, trace => (uniform (Bits request.length)).bind fun ciphertext =>
      beforeHaltLaw rounds state (some true :: past) ciphertext.toList ((request, ciphertext.toList) :: trace)

variable {State : Type u} (oracle : BitOracle State)

theorem run_before_halt (rounds : Nat) (state : State) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    TimedExecution.eval (FreshMaskAdaptiveRound.runtime oracle).step
      (rounds * (72 * request.length + 58) + 1)
      ((FreshMaskAdaptiveRound.runtime oracle).embed () (AdaptiveBitstringLoop.frame state rounds past request trace)) =
      (beforeHaltLaw rounds state past request trace).map ((FreshMaskAdaptiveRound.runtime oracle).embed ()) := by
  induction rounds generalizing past request trace with
  | zero =>
      cases request <;> simp [TimedExecution.eval, FreshMaskAdaptiveRound.runtime, CallerRuntime.packet,
        PacketResponseSource.step, beforeHaltLaw, AdaptiveBitstringLoop.frame,
        AdaptiveBitstringLoop.machine, ResponseLoading.loaded, ResponseLoading.fromCells,
        Reification.timedStep, Reification.terminal, Reification.perform, Reification.action, transition,
        AdaptiveBitstringLoop.code, Machine.Instruction.next, Machine.Configuration.tape,
        Machine.Configuration.advance, Tape.ofBits, PMF.pure_map]
  | succ rounds ih =>
      have hr := (FreshMaskAdaptiveRound.round oracle state rounds past request trace).law ()
        ((rounds + 1) * (72 * request.length + 58) + 1) (by
          rw [FreshMaskAdaptiveRound.round_budget]
          simp only [Nat.add_mul, Nat.one_mul]
          omega)
      rw [FreshMaskAdaptiveRound.round_entry, FreshMaskAdaptiveRound.round_costed,
        PMF.bind_map] at hr
      rw [hr, beforeHaltLaw, PMF.map_bind]
      congr 1
      funext ciphertext
      dsimp only [Function.comp_def]
      have ht : (rounds + 1) * (72 * request.length + 58) + 1 -
          (72 * request.length + 58) = rounds * (72 * ciphertext.toList.length + 58) + 1 := by
        rw [Bits.length_toList]
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      rw [ht]
      exact ih (some true :: past) ciphertext.toList ((request, ciphertext.toList) :: trace)

theorem beforeHaltLaw_active (rounds : Nat) (state : State) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) (frame : Configuration State)
    (hf : frame ∈ (beforeHaltLaw rounds state past request trace).support) :
    Reification.terminal frame.control = false := by
  induction rounds generalizing past request trace with
  | zero =>
      rw [beforeHaltLaw, PMF.mem_support_pure_iff] at hf
      subst frame
      rfl
  | succ rounds ih =>
      rw [beforeHaltLaw, PMF.mem_support_bind_iff] at hf
      obtain ⟨ciphertext, _, hf⟩ := hf
      exact ih (some true :: past) ciphertext.toList ((request, ciphertext.toList) :: trace) hf

/-- The full final physical state and its actual first halt time. -/
theorem first_halt_joint (rounds : Nat) (state : State) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    runToBoundary (FreshMaskAdaptiveRound.runtime oracle).step PacketResponseSource.terminal
      (timeBound rounds request.length)
      ((FreshMaskAdaptiveRound.runtime oracle).embed () (AdaptiveBitstringLoop.frame state rounds past request trace)) =
      (law rounds state past request trace).map (fun frame =>
        ((FreshMaskAdaptiveRound.runtime oracle).embed () frame, timeBound rounds request.length)) := by
  have ht : rounds * (72 * request.length + 58) + 1 + 1 = timeBound rounds request.length := by
    simp [timeBound, Nat.add_assoc]
  have h := runToBoundary_joint_of_adjacent (FreshMaskAdaptiveRound.runtime oracle).step
    PacketResponseSource.terminal
    ((FreshMaskAdaptiveRound.runtime oracle).embed () (AdaptiveBitstringLoop.frame state rounds past request trace))
    (rounds * (72 * request.length + 58) + 1)
    (PacketResponseSource.terminal_absorbing FreshMaskCallerService.componentStep
      FreshMaskCallerService.begin FreshMaskCallerService.ready AdaptiveBitstringLoop.code oracle)
    (by
      intro outer ho
      rw [run_before_halt, PMF.mem_support_map_iff] at ho
      obtain ⟨frame, hf, rfl⟩ := ho
      exact beforeHaltLaw_active rounds state past request trace frame hf)
    (by
      intro outer ho
      rw [ht, run oracle rounds state past request trace _ (Nat.le_refl _),
        PMF.mem_support_map_iff] at ho
      obtain ⟨frame, hf, rfl⟩ := ho
      exact (law_support rounds state past request trace frame hf).1)
  rw [ht, run oracle rounds state past request trace _ (Nat.le_refl _), PMF.map_comp] at h
  exact h

/-- Analysis fuel beyond completion does not change the actual halt time. -/
theorem first_halt_joint_of_le (rounds : Nat) (state : State) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) (fuel : Nat)
    (hFuel : timeBound rounds request.length ≤ fuel) :
    runToBoundary (FreshMaskAdaptiveRound.runtime oracle).step PacketResponseSource.terminal fuel
      ((FreshMaskAdaptiveRound.runtime oracle).embed () (AdaptiveBitstringLoop.frame state rounds past request trace)) =
      (law rounds state past request trace).map (fun frame =>
        ((FreshMaskAdaptiveRound.runtime oracle).embed () frame, timeBound rounds request.length)) := by
  have hj := first_halt_joint oracle rounds state past request trace
  rw [runToBoundary_fuel_stable (FreshMaskAdaptiveRound.runtime oracle).step PacketResponseSource.terminal
    (timeBound rounds request.length) fuel
    ((FreshMaskAdaptiveRound.runtime oracle).embed () (AdaptiveBitstringLoop.frame state rounds past request trace))
    hFuel ?_, hj]
  intro result hr
  rw [hj, PMF.mem_support_map_iff] at hr
  obtain ⟨frame, hf, he⟩ := hr
  rw [← he]
  exact (law_support rounds state past request trace frame hf).1

/-- The composed execution cost is exactly the unpadded first-halt cost. -/
theorem costed_is_first_halt (rounds : Nat) (state : State) (past : List (Option Bool))
    (request : List Bool) (trace : List (List Bool × List Bool)) :
    ((whole oracle rounds state past request trace).execution.costed ()).map
      (fun result => ((FreshMaskAdaptiveRound.runtime oracle).embed () result.1, result.2)) =
    runToBoundary (FreshMaskAdaptiveRound.runtime oracle).step PacketResponseSource.terminal
      (timeBound rounds request.length)
      ((FreshMaskAdaptiveRound.runtime oracle).embed () (AdaptiveBitstringLoop.frame state rounds past request trace)) := by
  rw [whole_costed, first_halt_joint, PMF.map_comp]
  rfl

end CryptoOracle.Interactive.FreshMaskAdaptiveExecution
