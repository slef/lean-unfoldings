module

public import Unfoldings.Geometry.HingeGapRadius

/-! Source-circle contacts below a hinge remain on the actual prefix held fixed. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

variable {n : ℕ} (R : PolygonalRay ℂ n) (outward : R.Outward) (nonzero : R.direction ≠ 0)

include outward nonzero in
theorem radialPoint_mem_prefix_of_radius_le (hinge : Fin (n + 1)) (r : ℝ≥0)
    (below : (r : ℝ) ≤ dist R.start (R.chain.vertex hinge)) :
    R.radialPoint outward nonzero r ∈
      Set.range (R.chain.interval 0 hinge.val (by omega)).path := by
  have whole := R.radialPoint_mem outward nonzero r
  have member := whole
  rw [R.carrier_split hinge] at member
  rcases member with prefix_member | suffix_member
  · exact prefix_member
  · have lower := R.suffix_radius_ge_hinge outward hinge suffix_member
    have radius : dist R.start (R.radialPoint outward nonzero r) = (r : ℝ) := by
      rw [dist_eq_norm', R.norm_radialPoint_sub_start]
    rw [radius] at lower
    have same := R.eq_of_radius_eq outward nonzero whole
      (Or.inl (R.chain.vertex_mem_path_range hinge)) (radius.trans (le_antisymm below lower))
    rw [same]
    have endpoint := (R.chain.interval 0 hinge.val (by omega)).vertex_mem_path_range (Fin.last _)
    simpa only [R.chain.interval_last, Nat.zero_add, Fin.eta] using endpoint

include outward nonzero in
/-- An inactive source circle, including the hinge circle, has the unchanged original contact. -/
theorem hingeCirclePoint_eq_of_below (hinge : Fin (n + 1)) (angle : ℝ)
    (radial : ∀ θ ∈ Set.Icc 0 angle, (R.rotateSuffix hinge θ).Outward)
    (r : ℝ≥0) (below : (r : ℝ) ≤ dist R.start (R.chain.vertex hinge))
    (θ : Set.Icc 0 angle) :
    R.hingeCirclePoint hinge nonzero angle radial r θ = R.radialPoint outward nonzero r := by
  have prefix_member := R.radialPoint_mem_prefix_of_radius_le outward nonzero hinge r below
  have rotated_prefix : R.radialPoint outward nonzero r ∈ Set.range
      ((R.rotateSuffix hinge θ.val).chain.interval 0 hinge.val (by omega)).path := by
    rwa [R.rotateSuffix_prefix]
  have whole : R.radialPoint outward nonzero r ∈ (R.rotateSuffix hinge θ.val).carrier := by
    rw [(R.rotateSuffix hinge θ.val).carrier_split hinge]
    exact Or.inl rotated_prefix
  apply (R.rotateSuffix hinge θ.val).eq_of_radius_eq (radial θ.val θ.property)
    (R.rotateSuffix_direction_ne_zero hinge θ.val nonzero)
    ((R.rotateSuffix hinge θ.val).radialPoint_mem (radial θ.val θ.property)
      (R.rotateSuffix_direction_ne_zero hinge θ.val nonzero) r) whole
  rw [R.rotateSuffix_start]
  change dist R.start (R.hingeCirclePoint hinge nonzero angle radial r θ) =
    dist R.start (R.radialPoint outward nonzero r)
  rw [R.hingeCirclePoint_radius, dist_eq_norm', R.norm_radialPoint_sub_start]

end Unfoldings.PolygonalRay
