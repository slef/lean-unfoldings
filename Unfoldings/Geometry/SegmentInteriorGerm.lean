module

public import Unfoldings.Geometry.SegmentEndpointGerm
public import Mathlib.Tactic.Module

/-! Exact two-sided original edge directions at interior segment points. -/

@[expose] public section

open Filter Topology

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A full direction line consists of its two original nonnegative rays. -/
theorem range_smul_eq_nonnegativeRays (direction : E) :
    Set.range (fun t : ℝ => t • direction) =
      nonnegativeRay direction ∪ nonnegativeRay (-direction) := by
  ext v
  constructor
  · rintro ⟨t, rfl⟩
    by_cases nonnegative : 0 ≤ t
    · exact Or.inl ⟨t, nonnegative, rfl⟩
    · refine Or.inr ⟨-t, neg_nonneg.mpr (le_of_not_ge nonnegative), ?_⟩
      simp only [neg_smul, smul_neg, neg_neg]
  · rintro (⟨t, _nonnegative, equal⟩ | ⟨t, _nonnegative, equal⟩)
    · exact ⟨t, equal.symm⟩
    · exact ⟨-t, by simpa only [neg_smul, smul_neg] using equal.symm⟩

/-- Around a strict interior point the exact segment is its full original direction line. -/
theorem eventually_mem_segment_iff_direction_line (a b : Plane) (different : a ≠ b)
    (t : ℝ) (bounds : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ z in 𝓝 (AffineMap.lineMap a b t), z ∈ segment ℝ a b ↔
      z - AffineMap.lineMap a b t ∈ Set.range (fun s : ℝ => s • (b - a)) := by
  have near : ∀ᶠ z in 𝓝 (AffineMap.lineMap a b t),
      lineCoordinate a b z ∈ Set.Ioo (0 : ℝ) 1 := by
    apply (lineCoordinate a b).continuous_of_finiteDimensional.continuousAt.tendsto.eventually
    rw [lineCoordinate_lineMap different]
    exact isOpen_Ioo.mem_nhds bounds
  filter_upwards [near] with z hz
  constructor
  · intro member
    rw [segment_eq_image_lineMap] at member
    obtain ⟨s, _bounds, rfl⟩ := member
    refine ⟨s - t, ?_⟩
    simp only [AffineMap.lineMap_apply_module']
    module
  · rintro ⟨s, equal⟩
    have expression : z = AffineMap.lineMap a b (t + s) := by
      have solve : z = s • (b - a) + AffineMap.lineMap a b t :=
        (eq_sub_iff_add_eq.mp equal).symm
      rw [solve]
      simp only [AffineMap.lineMap_apply_module']
      module
    rw [expression, lineCoordinate_lineMap different] at hz
    rw [expression]
    exact lineMap_mem_segment ℝ a b ⟨hz.1.le, hz.2.le⟩

/-- The actual interior edge germ has precisely the original forward and reverse directions. -/
theorem segment_cellGerm_interior (a b : Plane) (different : a ≠ b)
    (t : ℝ) (bounds : t ∈ Set.Ioo (0 : ℝ) 1) :
    AffineArrangement.cellGerm (segmentInequalities a b) (fun _ => true)
      (AffineMap.lineMap a b t) = nonnegativeRay (b - a) ∪ nonnegativeRay (a - b) := by
  apply eq_of_local_homogeneous_models (AffineMap.lineMap a b t)
    (fun v r positive => AffineArrangement.mem_cellGerm_smul_iff _ _ _ v positive)
    (fun v r positive => by simp only [Set.mem_union,
      mem_nonnegativeRay_smul_iff _ v positive])
  · simpa only [← segment_eq_closedChamber] using
      AffineArrangement.eventually_mem_closedChamber_iff_cellGerm
        (segmentInequalities a b) (fun _ => true) (AffineMap.lineMap a b t)
  · simpa only [range_smul_eq_nonnegativeRays, neg_sub] using
      eventually_mem_segment_iff_direction_line a b different t bounds

end Unfoldings
