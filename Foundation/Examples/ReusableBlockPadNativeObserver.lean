import Foundation.Examples.ReusableBlockPad
import Foundation.Crypto.Semantics.Machine.NativeObservers
import Foundation.Crypto.Semantics.Oracle.ReusableNativeObservation

/-! The arbitrary-width pad with an actual finite native observer. The
existing ciphertext tape is inherited, the private key/history remain outside
native access, and the ownership transfer and observer instructions are charged.
The observer may use randomBit and may have input-dependent running time. -/
namespace Foundation.Examples.ReusableBlockPad.NativeObserver
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC ResponseHandoffProgram
universe u v
set_option backward.isDefEq.respectTransparency false

abbrev RuntimeState (State : Type u) :=
  ReusableResponseInitialization.Control ResponseHandoff.Control State

abbrev boundary {State : Type u} : RuntimeState State → Bool := ReusableNativeObservation.boundary
abbrev publicMachine {State : Type u} : RuntimeState State → Machine.Configuration :=
  ReusableNativeObservation.publicMachine

variable {State : Type u} (oracle : BitOracle State) (state : State)
    (trace : List (List Bool × List Bool)) {width : Nat} (message : Bits width)

theorem absorbing (target : RuntimeState State) (h : boundary target = true) :
    step oracle state trace message target = PMF.pure target :=
  ReusableNativeObservation.absorbing componentStep ReusableResponse.begin ready
    Machine.OneTimePad.keygen FlaggedBlockXor.code code oracle (callerFrame state trace message) target h

noncomputable def completion :=
  Completion.ofProcedure (initialized oracle state trace message) rfl
    (terminal := fun target => boundary target = true)
    (by
      intro result hr
      rw [initialized_semantics, PMF.mem_support_map_iff] at hr
      obtain ⟨key, _, rfl⟩ := hr
      rfl)

/-- The full physical caller after encryption depends only on ciphertext.
Both tapes and their heads are specified, not just outputBits. -/
def publicCaller (ciphertext : List Bool) : Machine.Configuration :=
  {pc := 1, outputTape := ResponseLoading.loaded ciphertext, halted := true}

theorem public_exit (key : Bits width) :
    publicMachine ((completion oracle state trace message).execution.exit ()
      (.active (.source (retainedKey key.toList)
        ⟨state, .running (finalCaller key message), finalTrace trace key message⟩))) =
      publicCaller (OneTimePad.encrypt key message).toList := rfl

theorem completion_semantics :
    (completion oracle state trace message).execution.semantics () =
      (uniform (Bits width)).map (fun key =>
        ReusableResponseInitialization.Control.active
          (ReusableResponseSource.Control.source (retainedKey key.toList)
            ⟨state, .running (finalCaller key message), finalTrace trace key message⟩)) := by
  rw [completion, Completion.ofProcedure_semantics, initialized_semantics, PMF.map_comp]
  rfl

variable {Output : Type v} (Q : Machine.Procedure Machine.Configuration Output)
    (hEntry : ∀ machine, Q.execution.entry machine = machine.resumeAt 0)
    (hHalt : ∀ input output, output ∈ (Q.execution.semantics input).support →
      (Q.execution.exit input output).halted = true)
    (cap : Nat) (hCap : ∀ ciphertext : List Bool, ciphertext.length = width →
      Q.execution.budget (publicCaller ciphertext) ≤ cap)

include hCap in
theorem supported_cap (target : RuntimeState State)
    (h : target ∈ ((completion oracle state trace message).execution.semantics ()).support) :
    Q.execution.budget (publicMachine target) ≤ cap := by
  rw [completion_semantics, PMF.mem_support_map_iff] at h
  obtain ⟨key, _, rfl⟩ := h
  change Q.execution.budget (publicCaller (OneTimePad.encrypt key message).toList) ≤ cap
  exact hCap _ (Bits.length_toList _)

noncomputable def whole :=
  NativeContinuation.whole (step oracle state trace message) boundary publicMachine
    (completion oracle state trace message) (absorbing oracle state trace message) Q
    publicMachine (fun target => hEntry (publicMachine target)) cap
    (supported_cap oracle state trace message Q cap hCap)

theorem budget : (whole oracle state trace message Q hEntry cap hCap).budget () =
    55 * width + 42 + cap := by
  rw [whole, NativeContinuation.whole_budget]
  change (initialized oracle state trace message).budget () + 1 + cap = _
  rw [initialized_budget]

abbrev decision : NativeContinuation.Control (RuntimeState State) → Bool :=
  ReusableNativeObservation.decision

noncomputable def game (horizon : Nat) : PMF Bool :=
  (TimedExecution.eval (NativeContinuation.step (step oracle state trace message) boundary publicMachine Q.code)
    horizon (.producing ((initialized oracle state trace message).entry ()))).map decision

/-- The mathematical observer below is the semantics of the native program
on the already loaded ciphertext, with its running time separately charged. -/
noncomputable def observer (ciphertext : List Bool) : PMF Bool :=
  (Q.execution.semantics (publicCaller ciphertext)).map
    (fun output => (Q.execution.exit (publicCaller ciphertext) output).outputTape.current.getD false)

include hEntry hHalt hCap in
theorem game_eq (horizon : Nat) (hTime : 55 * width + 42 + cap ≤ horizon) :
    game oracle state trace message Q horizon =
      (ciphertext oracle state trace message (55 * width + 41)).bind (observer Q) := by
  have ht : (completion oracle state trace message).execution.budget () + 1 + cap ≤ horizon := by
    change (initialized oracle state trace message).budget () + 1 + cap ≤ horizon
    rw [initialized_budget]
    omega
  have h := NativeContinuation.run (step oracle state trace message) boundary publicMachine
    (completion oracle state trace message) (absorbing oracle state trace message) Q publicMachine
    (fun target => hEntry (publicMachine target)) hHalt cap
    (supported_cap oracle state trace message Q cap hCap) horizon ht
  have hg := congrArg (fun distribution => distribution.map decision) h
  rw [game, ciphertext_eq oracle state trace message _ (Nat.le_refl _)]
  change _ = _ at hg
  simpa only [completion_semantics,
    PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def, publicMachine, ReusableNativeObservation.publicMachine,
    finalCaller, caller, Machine.Configuration.advance, observer, publicCaller, decision, ReusableNativeObservation.decision] using hg

include hEntry hHalt hCap in
/-- Perfect secrecy now includes real native observer instructions and the
charged handoff. Different worlds may use different sufficient horizons. -/
theorem perfect_secrecy (other : Bits width) (leftTime rightTime : Nat)
    (hLeft : 55 * width + 42 + cap ≤ leftTime) (hRight : 55 * width + 42 + cap ≤ rightTime) :
    game oracle state trace message Q leftTime = game oracle state trace other Q rightTime := by
  rw [game_eq oracle state trace message Q hEntry hHalt cap hCap leftTime hLeft,
    game_eq oracle state trace other Q hEntry hHalt cap hCap rightTime hRight,
    ciphertext_uniform oracle state trace message _ (Nat.le_refl _),
    ciphertext_uniform oracle state trace other _ (Nat.le_refl _)]

theorem time_polynomial {width cap : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hObserver : PolynomiallyBounded cap) :
    PolynomiallyBounded (fun n => 55 * width n + 42 + cap n) :=
  (((PolynomiallyBounded.const 55).mul hWidth).add
    (PolynomiallyBounded.const 42)).add hObserver

/-- The random observer's result really is its freshly sampled bit. -/
theorem random_observer (ciphertext : List Bool) :
    observer NativeObservers.random ciphertext = sampleBit := by
  simp only [observer, NativeObservers.random, Machine.Procedure.ofFixed,
    TimedExecution.Procedure.ofFixed, PMF.map_comp, Function.comp_def]
  change sampleBit.map id = sampleBit
  exact PMF.map_id _

/-- The native first-cell observer implements the usual first-bit test,
including the specified false result on an empty ciphertext. -/
theorem first_observer (ciphertext : List Bool) :
    observer NativeObservers.first ciphertext = PMF.pure (ciphertext.headD false) := by
  simp only [observer, NativeObservers.first, Machine.Procedure.ofFixed,
    TimedExecution.Procedure.ofFixed, PMF.pure_map]
  cases ciphertext <;> rfl

/-- A single five-instruction program reads the first ciphertext cell for
all widths, including zero; encryption, transfer and observer cost 55W+45. -/
theorem first_secrecy (other : Bits width) (horizon : Nat)
    (hTime : 55 * width + 45 ≤ horizon) :
    game oracle state trace message NativeObservers.first horizon =
      game oracle state trace other NativeObservers.first horizon := by
  exact perfect_secrecy oracle state trace message NativeObservers.first (fun _ => rfl)
    NativeObservers.first_halted 3 (fun _ _ => Nat.le_refl _) other horizon horizon
    (by omega) (by omega)

/-- A native randomBit observer is also covered by the same composition and
secrecy theorem; its total upper bound is 55W+44. -/
theorem random_secrecy (other : Bits width) (horizon : Nat)
    (hTime : 55 * width + 44 ≤ horizon) :
    game oracle state trace message NativeObservers.random horizon =
      game oracle state trace other NativeObservers.random horizon := by
  exact perfect_secrecy oracle state trace message NativeObservers.random (fun _ => rfl)
    NativeObservers.random_halted 2 (fun _ _ => Nat.le_refl _) other horizon horizon
    (by omega) (by omega)

end Foundation.Examples.ReusableBlockPad.NativeObserver
