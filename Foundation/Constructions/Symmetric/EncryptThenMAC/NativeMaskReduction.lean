import Foundation.Constructions.Symmetric.EncryptThenMAC.GeneratedBlockMaskNativeObserverPRG
import Foundation.Examples.ReusableBlockPadNativeObserverResources

/-! Finite operational implementation of the PRG reduction after receipt of
one challenge. The entry requires the challenge already on the actual retained
input tape and the public flagged message already on the caller tape. Receipt
and loading of the challenge are separate charged operations, not hidden here.
Native masking, private-key copying, response loading and observer execution
are all performed by the fixed reusable runtime. -/
namespace Foundation.Symmetric.EncryptThenMAC.NativeMaskReduction
open Machine Foundation.Probability Foundation.Symmetric TimedExecution CryptoOracle.Interactive
open Foundation.Symmetric.EncryptThenMAC ResponseHandoffProgram
open Foundation.Examples
open ReusableBlockPad.NativeObserver (RuntimeState boundary publicMachine publicCaller decision observer)
universe u
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev oracle := ReusableBlockPadEncodedBackend.unitOracle
noncomputable abbrev sourceStep {width : Nat} (message : Bits width) :=
  ReusableBlockPad.step oracle () [] message

def initial {width : Nat} (key message : Bits width) : RuntimeState Unit :=
  .active (.source (retainedKey key.toList) (ReusableBlockPad.callerFrame () [] message))

variable {width : Nat} (key message : Bits width)

noncomputable def masking :=
  (ReusableBlockPad.whole oracle () [] key message).transport (sourceStep message)
    ReusableResponseInitialization.Control.active (fun _ => rfl)

noncomputable def completion :=
  Completion.ofProcedure (masking key message) rfl (terminal := fun target => boundary target = true)
    (by intro result _; rfl)

theorem completion_semantics :
    (completion key message).execution.semantics () =
      PMF.pure (ReusableResponseInitialization.Control.active
        (ReusableResponseSource.Control.source (retainedKey key.toList)
          ⟨(), .running (ReusableBlockPad.finalCaller key message), ReusableBlockPad.finalTrace [] key message⟩)) := by
  rw [completion, Completion.ofProcedure_semantics]
  change ((ReusableBlockPad.whole oracle () [] key message).semantics ()).map _ = _
  rw [ReusableBlockPad.whole_semantics, PMF.pure_map]
  rfl

variable {Output : Type u} (Q : Machine.Procedure Machine.Configuration Output)
    (hEntry : ∀ machine, Q.execution.entry machine = machine.resumeAt 0)
    (hHalt : ∀ machine output, output ∈ (Q.execution.semantics machine).support →
      (Q.execution.exit machine output).halted = true)
    (cap : Nat) (hCap : ∀ ciphertext : List Bool, ciphertext.length = width →
      Q.execution.budget (publicCaller ciphertext) ≤ cap)

include hCap in
theorem supported_cap (target : RuntimeState Unit)
    (h : target ∈ ((completion key message).execution.semantics ()).support) :
    Q.execution.budget (publicMachine target) ≤ cap := by
  rw [completion_semantics, PMF.mem_support_pure_iff] at h
  subst target
  change Q.execution.budget (publicCaller (OneTimePad.encrypt key message).toList) ≤ cap
  exact hCap _ (Bits.length_toList _)

noncomputable def whole :=
  NativeContinuation.whole (sourceStep message) boundary publicMachine (completion key message)
    (ReusableBlockPad.NativeObserver.absorbing oracle () [] message) Q publicMachine
    (fun target => hEntry (publicMachine target)) cap (supported_cap key message Q cap hCap)

theorem budget : (whole key message Q hEntry cap hCap).budget () = 49 * width + 36 + cap := by
  rw [whole, NativeContinuation.whole_budget]
  change (ReusableBlockPad.whole oracle () [] key message).budget () + 1 + cap = _
  rw [ReusableBlockPad.whole_budget]

def finish : RuntimeState Unit :=
  .active (.source (retainedKey key.toList)
    ⟨(), .running (ReusableBlockPad.finalCaller key message), ReusableBlockPad.finalTrace [] key message⟩)

theorem whole_semantics :
    (whole key message Q hEntry cap hCap).semantics () =
      (Q.execution.semantics (publicCaller (OneTimePad.encrypt key message).toList)).map
        (fun output => ((finish key message, ()), output)) := by
  rw [whole, NativeContinuation.whole_semantics, completion_semantics, PMF.pure_bind]
  rfl

theorem whole_exit (output : (RuntimeState Unit × Unit) × Output) :
    (whole key message Q hEntry cap hCap).exit () output =
      NativeContinuation.Control.observing output.1.1 (Q.execution.exit (publicMachine output.1.1) output.2) := rfl

noncomputable def game (horizon : Nat) : PMF Bool :=
  (TimedExecution.eval (NativeContinuation.step (sourceStep message) boundary publicMachine Q.code)
    horizon (.producing (initial key message))).map decision

include hEntry hHalt hCap in
/-- A whole finite execution computes XOR and runs the supplied native
observer; the mathematical XOR in the result has a charged implementation. -/
theorem game_eq (horizon : Nat) (hTime : 49 * width + 36 + cap ≤ horizon) :
    game key message Q horizon = observer Q (OneTimePad.encrypt key message).toList := by
  have ht : (completion key message).execution.budget () + 1 + cap ≤ horizon := by
    change (ReusableBlockPad.whole oracle () [] key message).budget () + 1 + cap ≤ horizon
    rw [ReusableBlockPad.whole_budget]
    omega
  have h := NativeContinuation.run (sourceStep message) boundary publicMachine (completion key message)
    (ReusableBlockPad.NativeObserver.absorbing oracle () [] message) Q publicMachine
    (fun target => hEntry (publicMachine target)) hHalt cap (supported_cap key message Q cap hCap) horizon ht
  have hg := congrArg (fun distribution => distribution.map decision) h
  change game key message Q horizon = _ at hg
  simpa only [completion_semantics, PMF.pure_bind, PMF.map_comp, Function.comp_def,
    publicMachine, ReusableNativeObservation.publicMachine, ReusableBlockPad.finalCaller,
    ReusableBlockPad.caller, Machine.Configuration.advance, observer, publicCaller,
    decision, ReusableNativeObservation.decision] using hg

include hEntry hHalt in
/-- The same finite code realizes either branch of the PRG reduction; the
chosen public message is part of the physical caller entry. -/
theorem reduce_eq (G : Generator) (n : Nat) (messages : G.Messages n) (side : Bool)
    (challenge : Bits (G.outputLength n))
    (hCap : ∀ ciphertext : List Bool, ciphertext.length = G.outputLength n →
      Q.execution.budget (publicCaller ciphertext) ≤ cap)
    (horizon : Nat) (hTime : 49 * G.outputLength n + 36 + cap ≤ horizon) :
    game challenge (G.message messages side) Q horizon =
      G.reduce messages side (fun ciphertext => observer Q ciphertext.toList) challenge := by
  rw [game_eq challenge (G.message messages side) Q hEntry hHalt cap hCap horizon hTime]
  unfold Generator.reduce OneTimePad.encrypt
  rw [Bits.xor_comm]

theorem time_polynomial {width observerCap : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hObserver : PolynomiallyBounded observerCap) :
    PolynomiallyBounded (fun n => 49 * width n + 36 + observerCap n) :=
  (((PolynomiallyBounded.const 49).mul hWidth).add (PolynomiallyBounded.const 36)).add hObserver

end Foundation.Symmetric.EncryptThenMAC.NativeMaskReduction
