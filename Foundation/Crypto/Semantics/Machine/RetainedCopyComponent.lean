import Foundation.Crypto.Semantics.Machine.NativeFixedComponent
import Foundation.Crypto.Semantics.Machine.RetainedCopy

/-! The existing cell-by-cell retained copy as a reusable finite component.
The source key and arbitrary inherited destination prefix are represented
physically at entry; preparation of that entry is not part of this contract. -/
namespace Machine.RetainedCopy.Component
open Foundation.Probability TimedExecution

abbrev Input := List Bool × List (Option Bool)

noncomputable def component : NativeComponent Input Configuration :=
  NativeComponent.ofFixed RetainedCopy.code (fun input => copying [] input.1 input.2)
    (fun _ output => output) (fun input => PMF.pure (finish input.1 input.2))
    (fun input => 8 * input.1.length + 5)
    (fun input => by simpa only [PMF.pure_map] using RetainedCopy.run input.1 input.2)
    (by decide) (fun _ => by change 0 < 12; decide) (fun _ => rfl)
    (by
      intro input output h
      rw [PMF.mem_support_pure_iff] at h
      subst output
      rfl)

theorem code : component.procedure.code = RetainedCopy.code := rfl

theorem budget (input : Input) : component.procedure.execution.budget input = 8 * input.1.length + 5 := rfl

theorem semantics (input : Input) : component.procedure.execution.semantics input =
    PMF.pure (finish input.1 input.2) := rfl

def bitBound (size : Nat) : Nat :=
  NativeEncodedResources.bound RetainedCopy.code 0 (size + 2) (8 * size + 5)

theorem space_polynomial : PolynomiallyBounded bitBound :=
  NativeEncodedResources.bound_polynomial _ (PolynomiallyBounded.const 0)
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 2))
    (((PolynomiallyBounded.const 8).mul PolynomiallyBounded.id).add (PolynomiallyBounded.const 5))

theorem storage_peak (input : Input) (elapsed : Nat) (hElapsed : elapsed ≤ 8 * input.1.length + 5)
    (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF RetainedCopy.code) elapsed
      (copying [] input.1 input.2)).support) :
    (NativeEncodedResources.completeEncoding.encode (RetainedCopy.code, target)).length ≤
      bitBound (input.1.length + input.2.length) := by
  have h := NativeEncodedResources.peak RetainedCopy.code _ elapsed hElapsed _ target hTarget
  have hi := Tape.cells_ofBits_le input.1
  have hCells : (copying [] input.1 input.2).tapeCells ≤ input.1.length + input.2.length + 2 := by
    change ({Tape.ofBits input.1 with left := []} : Tape).cells +
      ({left := input.2} : Tape).cells ≤ _
    simp only [Tape.cells, List.length_nil, Nat.zero_add]
    simp only [Tape.cells] at hi
    omega
  exact h.trans (NativeEncodedResources.bound_mono _ (Nat.le_refl 0) hCells (by omega))

end Machine.RetainedCopy.Component
