module

public import Unfoldings.Geometry.TriangleBoundaryRays
public import Unfoldings.Geometry.OppositeRayAngles

/-! At a noncorner of a triangle boundary, distinct genuine boundary rays are opposite. -/

@[expose] public section

namespace Unfoldings

theorem exists_smul_sub_of_mem_common_segment {E : Type*} [AddCommGroup E] [Module ℝ E]
    {a b p q : E} (first : p ∈ segment ℝ a b) (last : q ∈ segment ℝ a b) :
    ∃ t : ℝ, q - p = t • (b - a) := by
  rw [segment_eq_image_lineMap] at first last
  obtain ⟨s, _bounds, rfl⟩ := first
  obtain ⟨t, _bounds, rfl⟩ := last
  refine ⟨t - s, ?_⟩
  simp only [AffineMap.lineMap_apply_module']
  module

namespace Triangle

/-- Actual straight boundary segments at a noncorner have angle exactly pi. -/
theorem angle_boundary_rays_eq_pi (T : Triangle) {p x y : Plane}
    (noncorner : ¬ T.IsVertex p)
    (first : segment ℝ p x ⊆ frontier T.carrier)
    (last : segment ℝ p y ⊆ frontier T.carrier)
    (xne : x ≠ p) (yne : y ≠ p)
    (different : InnerProductGeometry.angle (x - p) (y - p) ≠ 0) :
    InnerProductGeometry.angle (x - p) (y - p) = Real.pi := by
  obtain ⟨e, first_edge⟩ := T.boundary_segment_subset_edge first
  obtain ⟨f, last_edge⟩ := T.boundary_segment_subset_edge last
  have same : e = f := by
    by_contra distinct
    exact noncorner (T.isVertex_of_mem_edges distinct
      (first_edge (left_mem_segment ℝ _ _)) (last_edge (left_mem_segment ℝ _ _)))
  subst f
  obtain ⟨a, outgoing⟩ := exists_smul_sub_of_mem_common_segment
    (first_edge (left_mem_segment ℝ _ _)) (first_edge (right_mem_segment ℝ _ _))
  obtain ⟨b, incoming⟩ := exists_smul_sub_of_mem_common_segment
    (last_edge (left_mem_segment ℝ _ _)) (last_edge (right_mem_segment ℝ _ _))
  have an : a ≠ 0 := by
    intro zero
    rw [zero, zero_smul] at outgoing
    exact xne (sub_eq_zero.mp outgoing)
  have bn : b ≠ 0 := by
    intro zero
    rw [zero, zero_smul] at incoming
    exact yne (sub_eq_zero.mp incoming)
  have nonzero : T.vertex (next e) - T.vertex e ≠ 0 :=
    sub_ne_zero.mpr (T.edge_endpoints_ne e).symm
  have opposite : a * b < 0 := by
    by_contra not_negative
    have positive := lt_of_le_of_ne (le_of_not_gt not_negative) (mul_ne_zero an bn).symm
    rw [outgoing, incoming] at different
    rcases mul_pos_iff.mp positive with ⟨ap, bp⟩ | ⟨an, bn⟩
    · exact different (by rw [InnerProductGeometry.angle_smul_left_of_pos _ _ ap,
        InnerProductGeometry.angle_smul_right_of_pos _ _ bp,
        InnerProductGeometry.angle_self nonzero])
    · exact different (by rw [InnerProductGeometry.angle_smul_left_of_neg _ _ an,
        InnerProductGeometry.angle_smul_right_of_neg _ _ bn,
        InnerProductGeometry.angle_neg_neg, InnerProductGeometry.angle_self nonzero])
  rw [outgoing, incoming]
  exact angle_smul_self_of_mul_neg nonzero opposite

end Triangle
end Unfoldings
