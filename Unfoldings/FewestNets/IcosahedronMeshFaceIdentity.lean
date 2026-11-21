module

public import Unfoldings.FewestNets.IcosahedronMeshCornerIdentity

/-! The fine triangles have distinct geometric labels. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open scoped BigOperators

private theorem fin_three_exists_ne (d : Fin 3) : ∃ k : Fin 3, d ≠ k := by
  have table : ∀ d : Fin 3, ∃ k : Fin 3, d ≠ k := by decide +kernel
  exact table d

theorem exists_gridWeights_min {q : ℕ} (t : MeshFace q) (i : Fin 12) :
    ∃ k : Fin 3, gridWeights t k i = gridMin t i := by
  by_cases hi : i ∈ Set.range (faceVertex t.1)
  · obtain ⟨d, rfl⟩ := hi
    obtain ⟨k, hk⟩ := fin_three_exists_ne d
    by_cases upper : t.2.val.2.2 = true
    · refine ⟨d, ?_⟩
      rw [gridWeights, gridMin, extendFaceWeights_faceVertex, extendFaceWeights_faceVertex]
      simp [localGridWeights, localGridMin, TriangleGrid.barycentricCorner, upper]
    · refine ⟨k, ?_⟩
      rw [gridWeights, gridMin, extendFaceWeights_faceVertex, extendFaceWeights_faceVertex]
      have lower : t.2.val.2.2 = false := Bool.eq_false_of_not_eq_true upper
      simp [localGridWeights, localGridMin, TriangleGrid.barycentricCorner, lower, hk]
  · refine ⟨0, ?_⟩
    rw [gridWeights, gridMin, extendFaceWeights_zero_of_outside _ _ hi,
      extendFaceWeights_zero_of_outside _ _ hi]

theorem exists_gridWeight_positive_iff {q : ℕ} (t : MeshFace q) (i : Fin 12) :
    (∃ k : Fin 3, 0 < gridWeights t k i) ↔ i ∈ Set.range (faceVertex t.1) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨k, pos⟩
    by_contra absent
    rw [gridWeights, extendFaceWeights_zero_of_outside _ _ absent] at pos
    omega
  · rintro ⟨d, rfl⟩
    obtain ⟨k, hk⟩ := fin_three_exists_ne d
    by_cases upper : t.2.val.2.2 = true
    · refine ⟨k, ?_⟩
      rw [gridWeights, extendFaceWeights_faceVertex]
      simp [localGridWeights, TriangleGrid.barycentricCorner, upper, hk]
    · refine ⟨d, ?_⟩
      rw [gridWeights, extendFaceWeights_faceVertex]
      have lower : t.2.val.2.2 = false := Bool.eq_false_of_not_eq_true upper
      simp [localGridWeights, TriangleGrid.barycentricCorner, lower]

private theorem gridMin_le_of_range_subset {q : ℕ} (hq : 0 < q) (t s : MeshFace q)
    (sub : Set.range (inscribedCorners s) ⊆ Set.range (inscribedCorners t))
    (i : Fin 12) : gridMin t i ≤ gridMin s i := by
  obtain ⟨k, hk⟩ := exists_gridWeights_min s i
  obtain ⟨l, same⟩ := sub (Set.mem_range_self k)
  have equal := congrFun (gridWeights_eq_of_inscribedCorners_eq hq t s l k same) i
  exact (gridWeights_bounds t l i).1.trans_eq (equal.trans hk)

private theorem faceVertex_range_subset_of_corner_range_subset {q : ℕ} (hq : 0 < q)
    (t s : MeshFace q) (sub : Set.range (inscribedCorners t) ⊆ Set.range (inscribedCorners s)) :
    Set.range (faceVertex t.1) ⊆ Set.range (faceVertex s.1) := by
  intro i hi
  obtain ⟨k, hk⟩ := (exists_gridWeight_positive_iff t i).mpr hi
  obtain ⟨l, same⟩ := sub (Set.mem_range_self k)
  have equal := congrFun (gridWeights_eq_of_inscribedCorners_eq hq s t l k same) i
  exact (exists_gridWeight_positive_iff s i).mp ⟨l, equal.symm ▸ hk⟩

private theorem gridCell_eq_of_min_eq {q : ℕ} (t s : GridCell q)
    (same : localGridMin t = localGridMin s) : t = s := by
  have first : t.val.1 = s.val.1 := Fin.ext (congrFun same 1)
  have second : t.val.2.1 = s.val.2.1 := Fin.ext (congrFun same 2)
  have t_total :
      (∑ i, localGridMin t i) + (if t.val.2.2 then 2 else 1) = q :=
    TriangleGrid.sum_barycentricMin t.property
  have s_total :
      (∑ i, localGridMin s i) + (if s.val.2.2 then 2 else 1) = q :=
    TriangleGrid.sum_barycentricMin s.property
  rw [same] at t_total
  have flavor : (if t.val.2.2 then 2 else 1) = (if s.val.2.2 then 2 else 1) :=
    Nat.add_left_cancel (t_total.trans s_total.symm)
  have third : t.val.2.2 = s.val.2.2 := by
    cases ht : t.val.2.2 <;> cases hs : s.val.2.2 <;> simp_all
  exact Subtype.ext (Prod.ext first (Prod.ext second third))

/-- Equal geometric triangles have the same macroface and grid label. -/
theorem meshFace_eq_of_corner_range_eq {q : ℕ} (hq : 0 < q) (t s : MeshFace q)
    (same : Set.range (inscribedCorners t) = Set.range (inscribedCorners s)) : t = s := by
  have sameFace := face_eq_of_corner_subset
    (faceVertex_range_subset_of_corner_range_subset hq t s same.le)
  have minEq : gridMin t = gridMin s := by
    funext i
    exact le_antisymm (gridMin_le_of_range_subset hq t s same.ge i)
      (gridMin_le_of_range_subset hq s t same.le i)
  apply Prod.ext sameFace
  apply gridCell_eq_of_min_eq
  funext d
  have h := congrFun minEq (faceVertex t.1 d)
  change extendFaceWeights t.1 (localGridMin t.2) (faceVertex t.1 d) =
    extendFaceWeights s.1 (localGridMin s.2) (faceVertex t.1 d) at h
  rw [extendFaceWeights_faceVertex, sameFace, extendFaceWeights_faceVertex] at h
  exact h

end Unfoldings.FewestNets.Icosahedron
