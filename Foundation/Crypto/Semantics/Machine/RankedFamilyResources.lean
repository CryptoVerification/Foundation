import Foundation.Crypto.Semantics.Machine.RankedFamily
import Foundation.Crypto.Semantics.Machine.NativeEncodedResources

/-! Resource certificates for any input-dependent ranked native family.
The representation includes the fixed code and complete physical state.
Polynomial profiles may range over arbitrary sets of valid inputs of each
size; logical proof labels are not represented as extra tape contents. -/
namespace Machine.Program.RankedFamily
open Foundation.Probability TimedExecution
universe u
variable {code : Program} {Input : Type u} (F : Program.RankedFamily code Input)

def bitBound (input : Input) : Nat :=
  NativeEncodedResources.bound code (F.entry input).pc (F.entry input).tapeCells
    ((F.ranking input).rank (F.entry input) + 1)

theorem storage_peak (input : Input) (elapsed : Nat)
    (hElapsed : elapsed ≤ (F.ranking input).rank (F.entry input) + 1)
    (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF code) elapsed (F.entry input)).support) :
    (NativeEncodedResources.completeEncoding.encode (code, target)).length ≤ F.bitBound input :=
  NativeEncodedResources.peak code _ elapsed hElapsed _ target hTarget

/-- A first-arrival outcome is bounded using its own reported time. -/
theorem storage_costed (input : Input) (result : Configuration × Nat)
    (hResult : result ∈ (F.execution.costed input).support) :
    (NativeEncodedResources.completeEncoding.encode (code, result.1)).length ≤
      NativeEncodedResources.bound code (F.entry input).pc (F.entry input).tapeCells result.2 := by
  rw [F.costed] at hResult
  exact NativeEncodedResources.boundary code Configuration.halted _ _ result hResult

def profile (pc cells time : Nat → Nat) (size : Nat) : Nat :=
  NativeEncodedResources.bound code (pc size) (cells size) (time size)

theorem profile_polynomial {pc cells time : Nat → Nat}
    (hPc : PolynomiallyBounded pc) (hCells : PolynomiallyBounded cells)
    (hTime : PolynomiallyBounded time) :
    PolynomiallyBounded (profile (code := code) pc cells time) :=
  NativeEncodedResources.bound_polynomial code hPc hCells hTime

/-- Uniformly covers every valid input at the chosen size, rather than
selecting a single representative input for the polynomial bound. -/
theorem storage_profile (pc cells time : Nat → Nat) (valid : Nat → Input → Prop)
    (hPc : ∀ size input, valid size input → (F.entry input).pc ≤ pc size)
    (hCells : ∀ size input, valid size input → (F.entry input).tapeCells ≤ cells size)
    (hTime : ∀ size input, valid size input →
      (F.ranking input).rank (F.entry input) + 1 ≤ time size)
    (size : Nat) (input : Input) (hValid : valid size input)
    (elapsed : Nat) (hElapsed : elapsed ≤ (F.ranking input).rank (F.entry input) + 1)
    (target : Configuration)
    (hTarget : target ∈ (TimedExecution.eval (stepPMF code) elapsed (F.entry input)).support) :
    (NativeEncodedResources.completeEncoding.encode (code, target)).length ≤
      profile (code := code) pc cells time size :=
  (F.storage_peak input elapsed hElapsed target hTarget).trans
    (NativeEncodedResources.bound_mono code (hPc size input hValid)
      (hCells size input hValid) (hTime size input hValid))

end Machine.Program.RankedFamily
