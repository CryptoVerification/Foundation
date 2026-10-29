import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitSeparation
import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitExperiment
import Foundation.Crypto.Semantics.Probability.ClassicalBitEightBitSharpWitness

/-! Finite comparisons for the exact eight-fair-bit joint experiments.
Observations include the secret key; these are not key-hidden advantages.
The separate verification runner records build completion and axiom audits. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
open scoped BigOperators

theorem table_experiment_edge_upper (u v : OrderedGridVertex 32)
    (he : faceEdge (orderedGridComplex 32) u v) (message : Bool) :
    tableEightBitJointDistance u v message ≤ 37 / 128 := by
  rw [tableEightBitJointDistance_eq_jointTV]
  exact table_five_key_edge_upper u v he message

theorem table_experiment_maximum_attained :
    ∃ u v, faceEdge (orderedGridComplex 32) u v ∧
      ∀ message, tableEightBitJointDistance u v message = 37 / 128 := by
  refine ⟨sharpTableChain 0, sharpTableChain 2, sharpTableChain_edge, ?_⟩
  intro message
  rw [tableEightBitJointDistance_eq_jointTV, sharpTableChain_jointTV]

/-- Every perfect four-key assignment with the prescribed boundary has a
larger distance on some actual edge, with an explicit quantitative gap. -/
theorem table_experiment_perfect_gap (d : OrderedGridVertex 32 → PerfectCipher (Fin 4))
    (hb : ∀ v, (∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) →
      (d v).signed = tableFourVector v) :
    ∃ u v, faceEdge (orderedGridComplex 32) u v ∧ ∀ message,
      tableEightBitJointDistance u v message + 145 / 384 ≤
        jointTV (d u).toCipher (d v).toCipher message := by
  obtain ⟨u, v, he, hl⟩ := table_four_key_obstruction d hb
  refine ⟨u, v, he, ?_⟩
  intro message
  have hu := table_experiment_edge_upper u v he message
  have hd := hl message
  linarith

noncomputable def tableEightBitImplementationDistance (u v : OrderedGridVertex 32) : ℝ :=
  max (tableEightBitJointDistance u v false) (tableEightBitJointDistance u v true)

theorem tableEightBitImplementationDistance_eq (u v : OrderedGridVertex 32) :
    tableEightBitImplementationDistance u v =
      implementationDistance (tableFiveCipher u).toCipher (tableFiveCipher v).toCipher := by
  simp only [tableEightBitImplementationDistance, tableEightBitJointDistance_eq_jointTV,
    implementationDistance]

theorem table_experiment_approximate_gap (c : OrderedGridVertex 32 → Cipher (Fin 4))
    (ε δ : OrderedGridVertex 32 → ℝ)
    (h0 : ∀ v, ∑ k, (c v).weight k * error0 (c v) k ≤ δ v)
    (h1 : ∀ v, ∑ k, (c v).weight k * error1 (c v) k ≤ δ v)
    (hp : ∀ v, |bias (signedContrast (c v))| ≤ ε v)
    (hm : ∀ v, ε v + 2 * δ v ≤ 1 / 8)
    (hb : ∀ v, (∃ k, (gridVertexPosition 32 (by omega) v).val k = 0) →
      repair (signedContrast (c v)) = tableFourVector v) :
    ∃ u v, faceEdge (orderedGridComplex 32) u v ∧
      tableEightBitImplementationDistance u v + 1 / 384 ≤
        implementationDistance (c u) (c v) := by
  obtain ⟨u, v, he, hgap⟩ := table_approximate_separation c ε δ h0 h1 hp hm hb
  refine ⟨u, v, he, ?_⟩
  rw [tableEightBitImplementationDistance_eq]
  exact hgap

end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
