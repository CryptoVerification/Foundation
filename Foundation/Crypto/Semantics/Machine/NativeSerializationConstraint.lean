import Foundation.Crypto.Semantics.Machine.NativeBoundaryObservation
import Foundation.Crypto.Semantics.Machine.RepresentationLayout
import Foundation.Crypto.Semantics.Machine.Adversary

/-! A native program cannot serialize unobservable finite blank padding.
Even state-dependent analysis budgets cannot reveal it once both executions
are proved to halt. A serializer needs a restricted layout or separately
represented metadata; an injective mathematical encoding alone is not code. -/
namespace Machine
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false

/-- Different completed horizons preserve equality of native bit outputs. -/
theorem output_eq_of_equivalent_completed (code : Program) (first second : Configuration)
    (equivalent : first.Equivalent second) (firstFuel secondFuel : Nat)
    (firstComplete : ∀ state ∈ (evalConfigWithin code first firstFuel).support, state.halted = true)
    (secondComplete : ∀ state ∈ (evalConfigWithin code second secondFuel).support, state.halted = true) :
    (evalConfigWithin code first firstFuel).map Configuration.outputBits =
      (evalConfigWithin code second secondFuel).map Configuration.outputBits := by
  have hFirst := evalConfigWithin_eq_of_le code first firstFuel (max firstFuel secondFuel) (le_max_left _ _)
    (fun state h => firstComplete state ((mem_support_evalConfigWithin_iff _ _ _ _).mpr h))
  have hSecond := evalConfigWithin_eq_of_le code second secondFuel (max firstFuel secondFuel) (le_max_right _ _)
    (fun state h => secondComplete state ((mem_support_evalConfigWithin_iff _ _ _ _).mpr h))
  rw [← hFirst, ← hSecond]
  exact evalConfigWithin_map_eq_of_equivalent code first second equivalent _ Configuration.outputBits
    (fun _ _ h => h.outputBits)

/-- A physical serializer must prove code execution, termination and output.
Its domain may restrict layouts. No mathematical encoder is executed for free. -/
structure NativeSerializer (domain : Configuration → Prop) (encode : Configuration → List Bool) where
  code : Program
  budget : Configuration → Nat
  complete : ∀ source, domain source → ∀ state ∈
    (evalConfigWithin code (source.resumeAt 0) (budget source)).support, state.halted = true
  realizes : ∀ source, domain source →
    (evalConfigWithin code (source.resumeAt 0) (budget source)).map Configuration.outputBits = PMF.pure (encode source)

namespace NativeSerializer

theorem encode_invariant {domain : Configuration → Prop} {encode : Configuration → List Bool}
    (S : NativeSerializer domain encode) (first second : Configuration)
    (hFirst : domain first) (hSecond : domain second) (equivalent : first.Equivalent second) :
    encode first = encode second := by
  have h := output_eq_of_equivalent_completed S.code (first.resumeAt 0) (second.resumeAt 0)
    (show (first.resumeAt 0).Equivalent (second.resumeAt 0) from
      ⟨rfl, rfl, equivalent.2.2.1, equivalent.2.2.2⟩) (S.budget first) (S.budget second)
    (S.complete first hFirst) (S.complete second hSecond)
  rw [S.realizes first hFirst, S.realizes second hSecond] at h
  have hSupport : encode first ∈ (PMF.pure (encode second)).support := by rw [← h]; simp
  simpa only [PMF.mem_support_pure_iff] using hSupport

/-- Exact serialization is possible only if cell equivalence identifies no distinct domain states. -/
theorem faithful_domain_separated {domain : Configuration → Prop} (E : FiniteBitEncoding Configuration)
    (S : NativeSerializer domain E.encode) (first second : Configuration)
    (hFirst : domain first) (hSecond : domain second) (equivalent : first.Equivalent second) : first = second :=
  E.encode_injective (S.encode_invariant first second hFirst hSecond equivalent)

end NativeSerializer

/-- The all-active-states domain contains indistinguishable redundant blank representations. -/
theorem no_unrestricted_native_serializer (E : FiniteBitEncoding Configuration) :
    ¬ Nonempty (NativeSerializer (fun state => state.halted = false) E.encode) := by
  rintro ⟨S⟩
  let first : Configuration := {}
  let second : Configuration := {inputTape := {right := [none]}}
  have hEquivalent : first.Equivalent second :=
    ⟨rfl, rfl, (Tape.blank_padding_equivalent [] 1).symm, Tape.Equivalent.refl _⟩
  have hEq := S.faithful_domain_separated E first second rfl rfl hEquivalent
  have hDifferent : first ≠ second := by decide
  exact hDifferent hEq

end Machine
