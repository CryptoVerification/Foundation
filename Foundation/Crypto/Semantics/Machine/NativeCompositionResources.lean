import Foundation.Crypto.Semantics.Machine.NativeCompositionReachability
import Foundation.Crypto.Semantics.Machine.NativeEncodedResources

/-! Whole-prefix and actual-cost endpoint storage for compiled native links.
The code representation is the linked source, including its added control
instructions. Valid input sets may contain all values at each size. -/
namespace Machine.TypedNativeComposition.Link
open Foundation.Probability TimedExecution
universe u v w x
variable {Input : Type u} {Output : Type v} {NextInput : Type w} {NextOutput : Type x}
    {P : Machine.Procedure Input Output} {Q : Machine.Procedure NextInput NextOutput}
    (L : Link P Q)

theorem native_entry (input : Input) : L.native.execution.entry input = P.execution.entry input := by
  change (P.execution.entry input).rebasePc 0 = _
  simp [Configuration.rebasePc]

def bitBound (input : Input) : Nat :=
  NativeEncodedResources.bound L.code (P.execution.entry input).pc (P.execution.entry input).tapeCells
    (P.execution.budget input + L.cap input + 1)

theorem storage_peak (input : Input) (elapsed : Nat)
    (hElapsed : elapsed ≤ P.execution.budget input + L.cap input + 1) (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF L.code) elapsed (P.execution.entry input)).support) :
    (NativeEncodedResources.completeEncoding.encode (L.code, target)).length ≤ L.bitBound input :=
  NativeEncodedResources.peak L.code _ elapsed hElapsed _ target hTarget

/-- An actual costed endpoint is bounded by its own time, even when the
two linked components have branches with different durations. -/
theorem storage_costed (input : Input) (result : Configuration × Nat)
    (hResult : result ∈ (L.native.execution.costed input).support) :
    (NativeEncodedResources.completeEncoding.encode (L.code, result.1)).length ≤
      NativeEncodedResources.bound L.code (P.execution.entry input).pc
        (P.execution.entry input).tapeCells result.2 := by
  have h := L.operational input result hResult
  change result.1 ∈ (TimedExecution.eval (stepPMF L.code) result.2 (L.native.execution.entry input)).support at h
  rw [L.native_entry] at h
  exact NativeEncodedResources.peak L.code result.2 result.2 (Nat.le_refl _) _ result.1 h

def storageProfile (pc cells firstTime secondTime : Nat → Nat) (size : Nat) : Nat :=
  NativeEncodedResources.bound L.code (pc size) (cells size) (firstTime size + secondTime size + 1)

theorem storageProfile_polynomial {pc cells firstTime secondTime : Nat → Nat}
    (hPc : PolynomiallyBounded pc) (hCells : PolynomiallyBounded cells)
    (hFirst : PolynomiallyBounded firstTime) (hSecond : PolynomiallyBounded secondTime) :
    PolynomiallyBounded (L.storageProfile pc cells firstTime secondTime) :=
  NativeEncodedResources.bound_polynomial L.code hPc hCells
    ((hFirst.add hSecond).add (PolynomiallyBounded.const 1))

theorem storage_profile (pc cells firstTime secondTime : Nat → Nat) (valid : Nat → Input → Prop)
    (hPc : ∀ size input, valid size input → (P.execution.entry input).pc ≤ pc size)
    (hCells : ∀ size input, valid size input → (P.execution.entry input).tapeCells ≤ cells size)
    (hFirst : ∀ size input, valid size input → P.execution.budget input ≤ firstTime size)
    (hSecond : ∀ size input, valid size input → L.cap input ≤ secondTime size)
    (size : Nat) (input : Input) (hValid : valid size input)
    (elapsed : Nat) (hElapsed : elapsed ≤ P.execution.budget input + L.cap input + 1)
    (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF L.code) elapsed (P.execution.entry input)).support) :
    (NativeEncodedResources.completeEncoding.encode (L.code, target)).length ≤
      L.storageProfile pc cells firstTime secondTime size :=
  (L.storage_peak input elapsed hElapsed target hTarget).trans
    (NativeEncodedResources.bound_mono L.code (hPc size input hValid) (hCells size input hValid)
      (Nat.add_le_add_right (Nat.add_le_add (hFirst size input hValid) (hSecond size input hValid)) 1))

end Machine.TypedNativeComposition.Link
