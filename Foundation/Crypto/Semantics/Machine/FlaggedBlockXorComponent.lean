import Foundation.Crypto.Semantics.Machine.NativeFixedComponent
import Foundation.Crypto.Semantics.Machine.FlaggedBlockXor
import Foundation.Crypto.Semantics.Machine.ResponseExport

/-! The flagged-message XOR algorithm as a reusable physical component.
The equal-length precondition is logical; it adds no runtime test or copying.
Every caller must establish the actual combined input tape at handoff. -/
namespace Machine.FlaggedBlockXor.Component
open Foundation.Probability TimedExecution

structure Input where
  key : List Bool
  message : List Bool
  sameLength : key.length = message.length

noncomputable def component : NativeComponent Input Configuration :=
  NativeComponent.ofFixed FlaggedBlockXor.code (fun input => initial input.key input.message)
    (fun _ output => output) (fun input => PMF.pure (final input.key input.message))
    (fun input => 24 * input.message.length + 8)
    (fun input => by simpa only [PMF.pure_map, FlaggedBlockXor.final] using FlaggedBlockXor.run input.key input.message input.sameLength)
    (by decide) (fun _ => by change 0 < 37; decide) (fun _ => rfl)
    (by
      intro input output h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      rfl)

theorem code : component.procedure.code = FlaggedBlockXor.code := rfl

theorem budget (input : Input) : component.procedure.execution.budget input = 24 * input.message.length + 8 := rfl

theorem semantics (input : Input) : component.procedure.execution.semantics input =
    PMF.pure (final input.key input.message) := rfl

theorem output (input : Input) (target : Configuration)
    (hTarget : target ∈ (component.procedure.execution.semantics input).support) :
    target.outputBits = OneTimePad.xorList input.key input.message := by
  rw [semantics, PMF.mem_support_pure_iff] at hTarget
  subst target
  exact final_output _ _

theorem initial_cells (input : Input) :
    (initial input.key input.message).tapeCells ≤ 3 * input.message.length + 3 := by
  change (ResponseExport.fromCells ((request input.message ++ input.key).map some ++ [none])).cells + 1 ≤ _
  have hc (packet : List Bool) : (ResponseExport.fromCells (packet.map some ++ [none])).cells = packet.length + 1 := by
    cases packet <;> simp [ResponseExport.fromCells, Tape.cells, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  rw [hc, List.length_append, request_length, input.sameLength]
  omega

def bitBound (size : Nat) : Nat :=
  NativeEncodedResources.bound FlaggedBlockXor.code 0 (3 * size + 3) (24 * size + 8)

theorem space_polynomial : PolynomiallyBounded bitBound :=
  NativeEncodedResources.bound_polynomial _ (PolynomiallyBounded.const 0)
    (((PolynomiallyBounded.const 3).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 3))
    (((PolynomiallyBounded.const 24).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 8))

theorem storage_peak (input : Input) (elapsed : Nat) (hElapsed : elapsed ≤ 24 * input.message.length + 8)
    (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF FlaggedBlockXor.code) elapsed
      (initial input.key input.message)).support) :
    (NativeEncodedResources.completeEncoding.encode (FlaggedBlockXor.code, target)).length ≤
      bitBound input.message.length :=
  (NativeEncodedResources.peak FlaggedBlockXor.code _ elapsed hElapsed _ target hTarget).trans
    (NativeEncodedResources.bound_mono _ (Nat.le_refl 0) (initial_cells input) (Nat.le_refl _))

end Machine.FlaggedBlockXor.Component
