module

public import Unfoldings.Geometry.SegmentInteriorGerm

/-! The terminal ray has both original line directions at every point beyond its source. -/

@[expose] public section

open Filter Topology
open scoped NNReal

namespace Unfoldings

/-- At a strictly positive ray parameter the endpoint inequality has actual positive clearance. -/
theorem eventually_mem_ray_iff_direction_line (a b : Plane) (different : a ≠ b)
    (t : ℝ) (positive : 0 < t) :
    ∀ᶠ z in 𝓝 (AffineMap.lineMap a b t),
      z ∈ Set.range (fun s : ℝ≥0 => AffineMap.lineMap a b (s : ℝ)) ↔
        z - AffineMap.lineMap a b t ∈ Set.range (fun s : ℝ => s • (b - a)) := by
  have near : ∀ᶠ z in 𝓝 (AffineMap.lineMap a b t), 0 < lineCoordinate a b z := by
    apply (lineCoordinate a b).continuous_of_finiteDimensional.continuousAt.tendsto.eventually
    rw [lineCoordinate_lineMap different]
    exact isOpen_Ioi.mem_nhds positive
  filter_upwards [near] with z hz
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨(s : ℝ) - t, ?_⟩
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
    exact ⟨(⟨t + s, hz.le⟩ : ℝ≥0), expression.symm⟩

/-- The actual terminal-ray cell germ beyond the source has both original directions. -/
theorem ray_cellGerm_interior (a b : Plane) (different : a ≠ b)
    (t : ℝ) (positive : 0 < t) :
    AffineArrangement.cellGerm (rayInequalities a b) (fun _ => true)
      (AffineMap.lineMap a b t) = nonnegativeRay (b - a) ∪ nonnegativeRay (a - b) := by
  apply eq_of_local_homogeneous_models (AffineMap.lineMap a b t)
    (fun v r positive => AffineArrangement.mem_cellGerm_smul_iff _ _ _ v positive)
    (fun v r positive => by simp only [Set.mem_union,
      mem_nonnegativeRay_smul_iff _ v positive])
  · simpa only [← ray_eq_closedChamber] using
      AffineArrangement.eventually_mem_closedChamber_iff_cellGerm
        (rayInequalities a b) (fun _ => true) (AffineMap.lineMap a b t)
  · simpa only [range_smul_eq_nonnegativeRays, neg_sub] using
      eventually_mem_ray_iff_direction_line a b different t positive

end Unfoldings
