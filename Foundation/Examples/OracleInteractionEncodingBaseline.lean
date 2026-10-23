import Foundation.Crypto.Semantics.Oracle.InteractionEncoding
import Foundation.Examples.OracleInteractionReplayBaseline

/-! Ordinary shared-lemma repair across input-dependent internal encodings.
The checker, supplied scripts, and existing plain probability lemmas are reused.
No diagram/cell/certificate module is imported by this baseline. -/
namespace CryptoOracle.ProofEdits.Interaction.Encoding.Baseline
open Foundation.Probability
set_option backward.isDefEq.respectTransparency false
variable {Input Tag : Type} [DecidableEq Input] [Fintype Tag] [Nonempty Tag]
    (codecs next : Input → Tag ≃ Tag)
    (seen : Finset Input) (first second : List (Action Input)) (positions : List Nat)
    (accepted : ReplayBaseline.validates seen first second positions = true)

include seen positions accepted in
theorem validated_run (stored : State Input Tag) : run codecs first stored = run codecs second stored :=
  transport codecs (ReplayBaseline.validates_kernel seen first second positions accepted) stored

include seen positions accepted in
theorem validated_invariant (stored final : State Input Tag)
    (known : Known seen stored) (coherent : Coherent stored)
    (supported : final ∈ (run codecs second stored).support) : Coherent final := by
  have plainKnown : Known seen (inverse codecs stored) := (known_state codecs seen _).mp (by
    simpa only [inverse_state] using known)
  have plainCoherent : Coherent (inverse codecs stored) := (coherent_state codecs _).mp (by
    simpa only [inverse_state] using coherent)
  have plainSupport : inverse codecs final ∈ (Interaction.run second (inverse codecs stored)).support := by
    rw [← run_inverse codecs second stored, PMF.mem_support_map_iff]
    exact ⟨final, supported, rfl⟩
  have finalCoherent := ReplayBaseline.validates_invariant seen first second positions accepted
    (inverse codecs stored) (inverse codecs final) plainKnown plainCoherent plainSupport
  have encoded := (coherent_state codecs (inverse codecs final)).mpr finalCoherent
  simpa only [inverse_state] using encoded

include seen positions accepted in
theorem validated_continuation {Result : Type} (stored : State Input Tag) (suffix : State Input Tag → PMF Result) :
    (run codecs first stored).bind suffix = (run codecs second stored).bind suffix := by
  rw [validated_run codecs seen first second positions accepted stored]

include seen positions accepted in
theorem validated_joint {Context : Type} (prefixLaw : PMF (Context × State Input Tag)) :
    (prefixLaw.bind fun original => (run codecs first original.2).map (fun final => (original, final))) =
      (prefixLaw.bind fun original => (run codecs second original.2).map (fun final => (original, final))) := by
  simp_rw [validated_run codecs seen first second positions accepted]

include seen positions accepted in
/-- The same script is reused across any TWO internal encodings. Only the
representation correspondence changes, by a uniform lemma shared by clients. -/
theorem repair (stored : State Input Tag) :
    (run codecs first stored).map (recode codecs next) = run next second (recode codecs next stored) := by
  rw [recode_run, validated_run next seen first second positions accepted]

include seen positions accepted in
/-- The selected correspondence also retains arbitrary prefix context,
including the original secret, while changing the internal representation. -/
theorem repair_joint {Context : Type} (prefixLaw : PMF (Context × State Input Tag)) :
    (prefixLaw.bind fun original => (run codecs first original.2).map
      (fun final => (original, recode codecs next final))) =
    (prefixLaw.bind fun original => (run next second (recode codecs next original.2)).map
      (fun final => (original, final))) := by
  congr 1
  funext original
  have transported := congrArg (PMF.map (fun final => (original, final)))
    (repair codecs next seen first second positions accepted original.2)
  simpa only [PMF.map_comp, Function.comp_def] using transported

end CryptoOracle.ProofEdits.Interaction.Encoding.Baseline
