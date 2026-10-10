import Foundation.Quantum.QKD.BB84Logic

/-! Concrete honest and eavesdropping BB84 dilations. Copying the computational
basis label is an isometry; it does not clone arbitrary unknown states. -/
namespace Foundation.Quantum.QKD.BB84Examples
noncomputable section
set_option backward.isDefEq.respectTransparency false

def honestDilation : Op .bit (.tensor .bit .bit) :=
  fun i j => if i.1 = j ∧ i.2 = 0 then 1 else 0

def copyZDilation : Op .bit (.tensor .bit .bit) :=
  fun i j => if i.1 = j ∧ i.2 = j then 1 else 0

theorem honest_isometry : honestDilation.conjTranspose * honestDilation = 1 := by
  ext i j
  change (∑ k : Fin 2 × Fin 2, star (honestDilation k i) * honestDilation k j) =
    if i = j then 1 else 0
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [honestDilation]

theorem copyZ_isometry : copyZDilation.conjTranspose * copyZDilation = 1 := by
  ext i j
  change (∑ k : Fin 2 × Fin 2, star (copyZDilation k i) * copyZDilation k j) =
    if i = j then 1 else 0
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [copyZDilation]

def honest : BB84Attack .bit := ⟨honestDilation, honest_isometry⟩
def copyZ : BB84Attack .bit := ⟨copyZDilation, copyZ_isometry⟩

theorem honest_zError (b : Fin 2) : honest.zError b = 0 := by
  fin_cases b <;> norm_num [BB84Attack.zError, honest, honestDilation, Fin.sum_univ_two,
    Space.Basis, Space.basisFintype]

theorem honest_xPlusError : honest.xPlusError = 0 := by
  norm_num [BB84Attack.xPlusError, honest, honestDilation, Fin.sum_univ_two,
    Space.Basis, Space.basisFintype]

theorem copyZ_zError (b : Fin 2) : copyZ.zError b = 0 := by
  fin_cases b <;> norm_num [BB84Attack.zError, copyZ, copyZDilation, Fin.sum_univ_two,
    Space.Basis, Space.basisFintype]

/-- The complementary test detects this eavesdropping attack with probability one half. -/
theorem copyZ_xPlusError : copyZ.xPlusError = 1 / 2 := by
  norm_num [BB84Attack.xPlusError, copyZ, copyZDilation, Fin.sum_univ_two,
    Space.Basis, Space.basisFintype, Complex.normSq]

/-- A computational-basis eavesdropper perfectly distinguishes the key bit. -/
theorem copyZ_environment_readout (b : Fin 2) :
    (basisEffect .bit b).probability (copyZ.environmentState b) = 1 := by
  rw [BB84Attack.basisEffect_probability]
  fin_cases b <;> norm_num [BB84Attack.environmentState, BB84Attack.environmentMatrix,
    copyZ, copyZDilation, Fin.sum_univ_two]

theorem copyZ_environment_other (b : Fin 2) :
    (basisEffect .bit (1 - b)).probability (copyZ.environmentState b) = 0 := by
  rw [BB84Attack.basisEffect_probability]
  fin_cases b <;> norm_num [BB84Attack.environmentState, BB84Attack.environmentMatrix,
    copyZ, copyZDilation, Fin.sum_univ_two]

/-- The three bound test hypotheses are verified by actual honest measurement probabilities. -/
theorem honest_tests : ∀ i,
    (BB84Logic.model (fun _ => honest)).Carrier ((BB84Logic.testContext 0).claim i) := by
  intro i
  fin_cases i
  · change (basisEffect .bit 1).probability (honest.bobChannel.run (basisDensity .bit 0)) = 0
    simpa only [← BB84Attack.zError_probability, sub_zero] using honest_zError 0
  · change (basisEffect .bit 0).probability (honest.bobChannel.run (basisDensity .bit 1)) = 0
    simpa only [← BB84Attack.zError_probability, sub_self] using honest_zError 1
  · exact (honest.xPlusError_probability).trans honest_xPlusError

/-- Interpretation of the actual no-information derivation. -/
theorem honest_proof_interpreted :
    (BB84Logic.model (fun _ => honest)).Carrier (.noInformation 0) :=
  BB84Logic.sound (fun _ => honest) (BB84Logic.complementaryProof 0) honest_tests

/-- Interpretation of the independent-key-state derivation, with all three tests verified. -/
theorem honest_ideal_key_interpreted :
    (BB84Logic.model (fun _ => honest)).Carrier (.idealKey 0) :=
  BB84Logic.sound (fun _ => honest) (BB84Logic.idealKeyProof 0) honest_tests

end
end Foundation.Quantum.QKD.BB84Examples
