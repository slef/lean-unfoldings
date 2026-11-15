module

public import Unfoldings.Geometry.RayInteriorGerm

/-! Every exact segment or ray germ uses only the original forward and reverse edge directions. -/

@[expose] public section

open scoped NNReal

namespace Unfoldings

/-- At any physical point, an actual segment contributes no directions off its original line. -/
theorem segment_cellGerm_subset_directions (a b x : Plane) :
    AffineArrangement.cellGerm (segmentInequalities a b) (fun _ => true) x ⊆
      nonnegativeRay (b - a) ∪ nonnegativeRay (a - b) := by
  classical
  by_cases member : x ∈ segment ℝ a b
  · by_cases different : a ≠ b
    · rw [segment_eq_image_lineMap] at member
      obtain ⟨t, bounds, rfl⟩ := member
      by_cases zero : t = 0
      · rw [zero, AffineMap.lineMap_apply_zero, segment_cellGerm_start]
        exact Set.subset_union_left
      · by_cases one : t = 1
        · rw [one, AffineMap.lineMap_apply_one, segment_cellGerm_finish]
          exact Set.subset_union_right
        · rw [segment_cellGerm_interior a b different t
            ⟨lt_of_le_of_ne bounds.1 (Ne.symm zero), lt_of_le_of_ne bounds.2 one⟩]
    · have same : a = b := not_ne_iff.mp different
      have at_source : x = a := by
        simpa only [same, segment_same, Set.mem_singleton_iff] using member
      rw [at_source, segment_cellGerm_start]
      exact Set.subset_union_left
  · have absent : x ∉ AffineArrangement.closedChamber (segmentInequalities a b)
        (fun _ => true) := by rwa [← segment_eq_closedChamber]
    simp only [AffineArrangement.cellGerm, ite_eq_right absent, Set.empty_subset]

/-- The same statement retains the entire unbounded original ray. -/
theorem ray_cellGerm_subset_directions (a b x : Plane) :
    AffineArrangement.cellGerm (rayInequalities a b) (fun _ => true) x ⊆
      nonnegativeRay (b - a) ∪ nonnegativeRay (a - b) := by
  classical
  by_cases member : x ∈ Set.range (fun t : ℝ≥0 => AffineMap.lineMap a b (t : ℝ))
  · by_cases different : a ≠ b
    · obtain ⟨t, rfl⟩ := member
      change AffineArrangement.cellGerm (rayInequalities a b) (fun _ => true)
        (AffineMap.lineMap a b (t : ℝ)) ⊆ _
      by_cases zero : (t : ℝ) = 0
      · rw [zero, AffineMap.lineMap_apply_zero, ray_cellGerm_start]
        exact Set.subset_union_left
      · rw [ray_cellGerm_interior a b different (t : ℝ)
          (lt_of_le_of_ne t.coe_nonneg (Ne.symm zero))]
    · have same : a = b := not_ne_iff.mp different
      have at_source : x = a := by
        obtain ⟨t, equal⟩ := member
        simpa only [same, AffineMap.lineMap_same, AffineMap.const_apply] using equal.symm
      rw [at_source, ray_cellGerm_start]
      exact Set.subset_union_left
  · have absent : x ∉ AffineArrangement.closedChamber (rayInequalities a b)
        (fun _ => true) := by rwa [← ray_eq_closedChamber]
    simp only [AffineArrangement.cellGerm, ite_eq_right absent, Set.empty_subset]

end Unfoldings
