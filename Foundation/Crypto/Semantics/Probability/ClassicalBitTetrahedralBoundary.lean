import Foundation.Crypto.Semantics.Probability.ClassicalBitNormalizedBoundary

/-! Concrete zero-avoidance certificates on the boundary of the four-vertex
simplex. Non-nullity of the normalized boundary map is not proved here. -/
namespace Foundation.Crypto.Semantics.Probability.ClassicalBitRepair

open scoped BigOperators
noncomputable section

def simplexBoundary (Vertex : Type*) [Fintype Vertex] : PreAbstractSimplicialComplex Vertex where
  faces := {cell | cell.Nonempty ∧ cell ≠ Finset.univ}
  isRelLowerSet_faces := by
    intro cell hc
    refine ⟨hc.1, ?_⟩
    intro face hsub hne
    refine ⟨hne, ?_⟩
    intro heq
    apply hc.2
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    apply hsub
    rw [heq]
    exact Finset.mem_univ v

theorem coordinate_separates_zero {Key : Type*} (s : Set (Key → ℝ)) (k : Key) (a : ℝ)
    (ha : a ≠ 0) (hs : ∀ v ∈ s, v k = a) : (0 : Key → ℝ) ∉ convexHull ℝ s := by
  have hconv : Convex ℝ {v : Key → ℝ | v k = a} := by
    intro x hx y hy b c _ _ hbc
    change b * x k + c * y k = a
    rw [hx, hy]
    rw [← add_mul, hbc, one_mul]
  have hsubset : convexHull ℝ s ⊆ {v : Key → ℝ | v k = a} :=
    convexHull_min hs hconv
  intro hzero
  have h := hsubset hzero
  change (0 : ℝ) = a at h
  exact ha h.symm

theorem sharpTetrahedron_face_avoids_zero (cell : Finset (Fin 4))
    (hc : cell ∈ simplexBoundary (Fin 4)) :
    (0 : Fin 4 → ℝ) ∉ convexHull ℝ
      ((fun i => (sharpTetrahedron i).signed) '' (cell : Set (Fin 4))) := by
  have hex : ∃ k, k ∉ cell := by
    by_contra h
    push Not at h
    exact hc.2 (Finset.eq_univ_iff_forall.mpr h)
  obtain ⟨k, hk⟩ := hex
  apply coordinate_separates_zero _ k (1 / 6) (by norm_num)
  rintro _ ⟨i, hi, rfl⟩
  have hne : k.val ≠ i.val := by
    intro heq
    have heqi : k = i := Fin.ext heq
    exact hk (heqi.symm ▸ hi)
  change (if k.val = i.val then -1 / 2 else 1 / 6 : ℝ) = 1 / 6
  rw [if_neg hne]

def sharpNormalizedBoundary : C(Realization (simplexBoundary (Fin 4)), PerfectVector (Fin 4)) :=
  normalizedBoundary (simplexBoundary (Fin 4)) sharpTetrahedron sharpTetrahedron_face_avoids_zero

def sharpEdgeMidpoint (k : Fin 4) : ℝ :=
  (1 / 2) * (sharpTetrahedron 0).signed k + (1 / 2) * (sharpTetrahedron 1).signed k

private theorem fin4_ne20 : (2 : Fin 4) ≠ 0 := by decide
private theorem fin4_ne30 : (3 : Fin 4) ≠ 0 := by decide

theorem sharpEdgeMidpoint_coordinates :
    sharpEdgeMidpoint = ![-1 / 6, -1 / 6, 1 / 6, 1 / 6] := by
  funext k
  fin_cases k <;> norm_num [sharpEdgeMidpoint, sharpTetrahedron, fin4_ne20, fin4_ne30]

theorem sharpEdgeMidpoint_mass : mass sharpEdgeMidpoint = 2 / 3 := by
  rw [sharpEdgeMidpoint_coordinates]
  norm_num [mass, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

theorem sharpEdgeMidpoint_normalized :
    normalizeSigned sharpEdgeMidpoint = ![-1 / 4, -1 / 4, 1 / 4, 1 / 4] := by
  funext k
  dsimp [normalizeSigned]
  rw [sharpEdgeMidpoint_mass, sharpEdgeMidpoint_coordinates]
  fin_cases k <;> norm_num

def sharpMidpointPoint : Realization (simplexBoundary (Fin 4)) :=
  ⟨![1 / 2, 1 / 2, 0, 0], by
    refine ⟨?_, ?_, {0, 1}, ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
    · exact ⟨by decide, by decide⟩
    · intro i hi
      fin_cases i
      · simp
      · simp
      · norm_num [Matrix.cons_val_two] at hi
      · norm_num [Matrix.cons_val_three] at hi⟩

theorem interpolate_sharp_midpoint :
    interpolate (simplexBoundary (Fin 4)) (fun i => (sharpTetrahedron i).signed)
      sharpMidpointPoint = sharpEdgeMidpoint := by
  funext k
  norm_num [interpolate, sharpMidpointPoint, Fin.sum_univ_four, Matrix.cons_val_two,
    Matrix.cons_val_three, sharpEdgeMidpoint]

theorem sharp_boundary_midpoint_nonunit :
    mass (interpolate (simplexBoundary (Fin 4)) (fun i => (sharpTetrahedron i).signed)
      sharpMidpointPoint) ≠ 1 := by
  rw [interpolate_sharp_midpoint, sharpEdgeMidpoint_mass]
  norm_num

theorem sharp_boundary_midpoint_normalized :
    (sharpNormalizedBoundary sharpMidpointPoint).val = ![-1 / 4, -1 / 4, 1 / 4, 1 / 4] := by
  change normalizeSigned (interpolate (simplexBoundary (Fin 4))
    (fun i => (sharpTetrahedron i).signed) sharpMidpointPoint) = _
  rw [interpolate_sharp_midpoint, sharpEdgeMidpoint_normalized]

/-- Zero avoidance and boundary inclusion are concrete here. Non-nullity is
still a premise, so this is not a completed non-nullity certificate. -/
theorem sharp_boundary_conditional_edge
    (hnonnull : ¬sharpNormalizedBoundary.Nullhomotopic) :
    ∃ u v, faceEdge (⊤ : PreAbstractSimplicialComplex (Fin 4)) u v ∧
      ∀ message, 2 / 3 ≤ jointTV (sharpTetrahedron u).toCipher
        (sharpTetrahedron v).toCipher message := by
  apply normalized_cone_perfect_edge (simplexBoundary (Fin 4)) ⊤ le_top 0
    (by exact Finset.singleton_nonempty _) ?_ sharpTetrahedron
    sharpTetrahedron_face_avoids_zero hnonnull
  intro cell _
  exact Finset.insert_nonempty _ _

end
end Foundation.Crypto.Semantics.Probability.ClassicalBitRepair
