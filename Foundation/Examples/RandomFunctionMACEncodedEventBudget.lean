import Foundation.Examples.RandomFunctionMACSharedEventBudget
import Foundation.Crypto.Semantics.Probability.Coupling

/-! 256 reversible tag encodings of one complete adaptive MAC transcript.
The common bad event supports simultaneous and transcript-dependent selection
of views. No independent execution is replaced by a copied sample. -/
namespace Foundation.Examples.RandomFunctionMACEncodedEventBudget
open Foundation.Probability CryptoOracle
open CryptoLogic.Polygraph.Experiment.GameCoherence.Requirements JointEventBudget
open RandomFunctionMACSharedEventBudget
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

abbrev Out := Transcript (Fin 8) (Fin 256)

def encode (offset : Fin 256) (out : Out) : Out :=
  { out with state := out.state.map (fun entry => (entry.1, entry.2 + offset))
             trace := out.trace.map (fun entry => (entry.1, entry.2 + offset)) }

def decode (offset : Fin 256) (out : Out) : Out :=
  { out with state := out.state.map (fun entry => (entry.1, entry.2 - offset))
             trace := out.trace.map (fun entry => (entry.1, entry.2 - offset)) }

theorem decode_encode (offset : Fin 256) (out : Out) : decode offset (encode offset out) = out := by
  cases out
  simp [decode, encode, List.map_map, Function.comp_def]

theorem encode_injective (offset : Fin 256) : Function.Injective (encode offset) :=
  Function.LeftInverse.injective (decode_encode offset)

def encodedModel : Realization (layout 256) Out (Fin 256 × Out) where
  value := fun vertex out => (vertex.1, encode vertex.1 (if vertex.2 then erase out else out))
  bad := fun _ out => out.result.1 = true
  root := by
    intro index out good
    change (index, encode index out) = (index, encode index (erase out))
    rw [erase_eq out (good () (by simp [layout]))]

theorem failure_iff (out : Out) : failure encodedModel (requests 256) out ↔ out.result.1 = true := by
  constructor
  · rintro ⟨index, different⟩
    apply (different_iff out).mp
    intro equal
    exact different (congrArg (fun value => (index, encode index value)) equal)
  · intro accepted
    refine ⟨0, ?_⟩
    intro equal
    have decoded := encode_injective 0 (congrArg Prod.snd equal)
    exact (different_iff out).mpr accepted decoded

theorem simultaneous_bound (attack : Program (Fin 8) (Fin 256) (Fin 8 × Fin 256)) :
    eventProb (law attack) (failure encodedModel (requests 256)) ≤ (256 : ℝ≥0∞)⁻¹ := by
  have localBound : ∀ label ∈ support (requests 256),
      eventProb (law attack) (encodedModel.bad label) ≤ (256 : ℝ≥0∞)⁻¹ := by
    intro _ _
    simpa only [law, encodedModel, Fintype.card_fin, Nat.cast_ofNat] using
      Foundation.Symmetric.RandomFunctionMACProofEdits.before_bound attack [] []
        (by intro entry member; cases member)
  have bound := family_bound encodedModel (requests 256) (law attack) (fun _ => (256 : ℝ≥0∞)⁻¹) localBound
  rw [support_singleton 256 (by decide)] at bound
  simpa only [SharedEventBudget.budget, Finset.sum_singleton] using bound

/-- Selection may depend on the full table, signing history and public trace.
No union factor is charged for these 256 views of the same execution. -/
theorem adaptive_selection_bound (attack : Program (Fin 8) (Fin 256) (Fin 8 × Fin 256))
    (choose : Out → Fin 256) :
    eventProb (law attack) (fun out =>
      encodedModel.value (requests 256 (choose out)).source out ≠
      encodedModel.value (requests 256 (choose out)).target out) ≤ (256 : ℝ≥0∞)⁻¹ :=
  (eventProb_mono (law attack) (fun out different => ⟨choose out, different⟩)).trans (simultaneous_bound attack)

/-- Both routes use the same local MAC lemma. Per-view union accounting
exports 1; the common-event accounting exports 1/256. -/
theorem occurrence_bound (attack : Program (Fin 8) (Fin 256) (Fin 8 × Fin 256)) :
    eventProb (law attack) (failure encodedModel (requests 256)) ≤
      ∑ _index : Fin 256, (256 : ℝ≥0∞)⁻¹ := by
  have same : failure encodedModel (requests 256) = failure (model 256) (requests 256) := by
    funext out
    apply propext
    exact (failure_iff out).trans (RandomFunctionMACSharedEventBudget.failure_iff 256 (by decide) out).symm
  rw [same]
  simpa [nsmul_eq_mul] using RandomFunctionMACSharedEventBudget.occurrence_bound 256 attack

def guessAttack : Program (Fin 8) (Fin 256) (Fin 8 × Fin 256) := .done (0, 0)

theorem guess_success_exact : eventProb (law guessAttack) (fun out => out.result.1 = true) = (256 : ℝ≥0∞)⁻¹ := by
  simp only [law, guessAttack, Foundation.Symmetric.RandomFunctionMACProofEdits.before,
    ProofEdits.Command.run, ProofEdits.Command.compile, Program.run, PMF.pure_map]
  change eventProb ((RandomOracle.oracle ([] : RandomOracle.Table (Fin 8) (Fin 256)) 0).map
    (fun response => (⟨(decide ((0 : Fin 8) ∉ []) && decide (response.2 = 0), []),
      response.1, [(0, response.2)]⟩ : Out))) (fun out => out.result.1 = true) = _
  rw [eventProb_map]
  have exactGuess := RandomOracle.fresh_guess ([] : RandomOracle.Table (Fin 8) (Fin 256)) 0 0 (by rfl)
  rw [eventProb_map] at exactGuess
  simpa [Fintype.card_fin] using exactGuess

/-- The improved bound is attained, so it is not merely a smaller displayed
expression disconnected from the actual joint failure probability. -/
theorem simultaneous_exact : eventProb (law guessAttack) (failure encodedModel (requests 256)) = (256 : ℝ≥0∞)⁻¹ := by
  have same : failure encodedModel (requests 256) = (fun out : Out => out.result.1 = true) := by
    funext out
    exact propext (failure_iff out)
  rw [same]
  exact guess_success_exact

def leftBundle (out : Out) (index : Fin 256) : Fin 256 × Out := (index, encode index out)
def rightBundle (out : Out) (index : Fin 256) : Fin 256 × Out := (index, encode index (erase out))

/-- A single bound for ANY event on all 256 jointly observed encodings.
This is stronger than a collection of marginal event bounds. -/
theorem joint_observation_gap (attack : Program (Fin 8) (Fin 256) (Fin 8 × Fin 256))
    (event : (Fin 256 → Fin 256 × Out) → Prop) :
    probabilityGap (eventProb ((law attack).map leftBundle) event)
      (eventProb ((law attack).map rightBundle) event) ≤ (256 : ℝ≥0∞)⁻¹ := by
  rw [eventProb_map, eventProb_map]
  apply (coupled_event_gap_le (law attack) _ _ (fun out => out.result.1 = true) ?_).trans
  · simpa only [law, Fintype.card_fin, Nat.cast_ofNat] using
      Foundation.Symmetric.RandomFunctionMACProofEdits.before_bound attack [] []
        (by intro entry member; cases member)
  · intro out _ good
    have same : leftBundle out = rightBundle out := by
      funext index
      simp only [leftBundle, rightBundle, erase_eq out good]
    rw [same]

/-- One observer attains the bound on a concrete no-signing forgery. -/
theorem joint_gap_exact :
    probabilityGap
      (eventProb ((law guessAttack).map leftBundle) (fun views => (views 0).2.result.1 = true))
      (eventProb ((law guessAttack).map rightBundle) (fun views => (views 0).2.result.1 = true)) = (256 : ℝ≥0∞)⁻¹ := by
  rw [eventProb_map, eventProb_map]
  change probabilityGap (eventProb (law guessAttack) (fun out => out.result.1 = true))
    (eventProb (law guessAttack) (fun _ => false = true)) = _
  rw [guess_success_exact]
  simp [eventProb, probabilityGap]

end Foundation.Examples.RandomFunctionMACEncodedEventBudget
