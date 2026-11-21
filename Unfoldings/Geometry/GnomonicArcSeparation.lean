module

public import Unfoldings.Geometry.GnomonicDistanceBounds
public import Unfoldings.Geometry.GnomonicMinorArc
public import Unfoldings.Geometry.SegmentClosestEndpoint

/-! Two close disjoint minor arcs in a gnomonic chart have a close endpoint. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open Set InnerProductGeometry

/-- Proximity anywhere on two disjoint arcs yields an endpoint-to-arc
distance at most the original angular distance times the chart distortion. -/
theorem exists_arcEndpoint_pair_angle_le (a b c d : Plane) {x y : Space}
    (disjoint : Disjoint (closedMinorArc (gnomonicNormal a) (gnomonicNormal b))
      (closedMinorArc (gnomonicNormal c) (gnomonicNormal d)))
    (hx : x ∈ closedMinorArc (gnomonicNormal a) (gnomonicNormal b))
    (hy : y ∈ closedMinorArc (gnomonicNormal c) (gnomonicNormal d))
    {k : ℝ} (kp : 0 < k) (kl : k ≤ 1) (xheight : k ≤ x 2) (yheight : k ≤ y 2) :
    ∃ x' ∈ closedMinorArc (gnomonicNormal a) (gnomonicNormal b),
      ∃ y' ∈ closedMinorArc (gnomonicNormal c) (gnomonicNormal d),
        (x' = gnomonicNormal a ∨ x' = gnomonicNormal b ∨
          y' = gnomonicNormal c ∨ y' = gnomonicNormal d) ∧
        angle x' y' ≤ (k ^ 2)⁻¹ * angle x y := by
  rw [← gnomonicNormal_image_segment, ← gnomonicNormal_image_segment] at disjoint
  have planar_disjoint : Disjoint (segment ℝ a b) (segment ℝ c d) := by
    refine Set.disjoint_left.mpr (fun r hr hs => ?_)
    exact Set.disjoint_left.mp disjoint ⟨r, hr, rfl⟩ ⟨r, hs, rfl⟩
  rw [← gnomonicNormal_image_segment] at hx hy
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  obtain ⟨p', hp', q', hq', endpoint, near⟩ :=
    exists_endpoint_minimizing_segment_dist planar_disjoint
  refine ⟨gnomonicNormal p', ?_, gnomonicNormal q', ?_, ?_, ?_⟩
  · rw [← gnomonicNormal_image_segment]
    exact ⟨p', hp', rfl⟩
  · rw [← gnomonicNormal_image_segment]
    exact ⟨q', hq', rfl⟩
  · rcases endpoint with rfl | rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr rfl))
  · exact (angle_gnomonicNormal_le_dist p' q').trans ((near p hp q hq).trans
      (dist_le_inv_sq_mul_gnomonicAngle p q kp kl xheight yheight))

end Unfoldings.Cap
