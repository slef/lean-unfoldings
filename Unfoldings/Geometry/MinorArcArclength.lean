module

public import Unfoldings.Geometry.EquatorialMinorArc
public import Unfoldings.Geometry.SphericalEndpointLocality

/-! Intrinsic arclength coordinates and outward tangents of actual minor arcs. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open InnerProductGeometry SpatialRotation Real

theorem closedMinorArc_comm (u v : Space) : closedMinorArc u v = closedMinorArc v u := by
  have open_comm (a b : Space) : openMinorArc a b ⊆ openMinorArc b a := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    rw [show (1 : ℝ) - (1 - t) = t by ring, add_comm]
  simp only [closedMinorArc, (open_comm u v).antisymm (open_comm v u), Set.insert_comm]

/-- The unit tangent at the first endpoint, directed along the minor arc toward the second. -/
def minorArcTangent (u v : Space) : Space :=
  (sin (angle u v))⁻¹ • (v - cos (angle u v) • u)

private theorem greatCirclePoint_complexLift_polarRay (a t : ℝ) :
    greatCirclePoint (complexLift (polarRay a)) (complexLift (polarRay (a + π / 2))) t =
      complexLift (polarRay (a + t)) := by
  have combo := polarRay_span_identity a (a + π / 2) (a + t)
  rw [show a + π / 2 - a = π / 2 by ring, sin_pi_div_two, one_smul,
    show a + π / 2 - (a + t) = π / 2 - t by ring, sin_pi_div_two_sub,
    show a + t - a = t by ring] at combo
  rw [greatCirclePoint, combo, map_add, map_smul, map_smul]

/-- The minor arc between unit endpoints is parametrized by arclength from its
first endpoint, with its canonical unit tangent orthogonal to that endpoint. -/
theorem closedMinorArc_arclength {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (positive : 0 < angle u v) (small : angle u v < π) :
    ‖minorArcTangent u v‖ = 1 ∧ inner ℝ u (minorArcTangent u v) = 0 ∧
      closedMinorArc u v = greatCirclePoint u (minorArcTangent u v) '' Set.Icc 0 (angle u v) := by
  obtain ⟨g, start, finish⟩ := exists_centered_arc_rotation hu hv
  let r := angle u v / 2
  let circle (t : ℝ) := complexLift (polarRay t)
  let w := minorArcTangent u v
  have u_frame : linear g u = circle (-r) := start.trans (equatorPoint_coe_eq_complexLift _)
  have v_frame : linear g v = circle r := finish.trans (equatorPoint_coe_eq_complexLift _)
  have sine : 0 < sin (angle u v) := sin_pos_of_pos_of_lt_pi positive small
  have w_frame : linear g w = circle (-r + π / 2) := by
    change linear g ((sin (angle u v))⁻¹ • (v - cos (angle u v) • u)) = _
    rw [map_smul, map_sub, map_smul, u_frame, v_frame]
    have v_eq : circle r = greatCirclePoint (circle (-r)) (circle (-r + π / 2)) (angle u v) := by
      rw [greatCirclePoint_complexLift_polarRay]
      congr 1
      dsimp [r]
      ring
    rw [v_eq, greatCirclePoint, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ sine.ne', one_smul]
  have w_unit : ‖w‖ = 1 := by
    rw [← (isometry g).norm_map w]
    change ‖linear g w‖ = 1
    rw [w_frame, complexLift.norm_map, norm_polarRay]
  have tangent : inner ℝ u w = 0 := by
    rw [inner_eq_cos_angle_of_norm_eq_one hu w_unit]
    have θ : angle u w = π / 2 := by
      rw [← (isometry g).toLinearIsometry.angle_map u w]
      change angle (linear g u) (linear g w) = _
      rw [u_frame, w_frame, complexLift.angle_map,
        angle_polarRay _ _ (by linarith [pi_pos]) (by linarith [pi_pos])]
      ring
    rw [θ, cos_pi_div_two]
  refine ⟨w_unit, tangent, ?_⟩
  have image_arc : linear g '' closedMinorArc u v = circle '' Set.Icc (-r) r := by
    rw [image_closedMinorArc, start, finish, ← equatorialArc_eq_closedMinorArc
      (r := r) (by dsimp [r]; positivity) (by dsimp [r]; linarith),
      equatorialArc_eq_image_complexLift (by dsimp [r]; linarith [pi_pos])]
  have map_point (t : ℝ) : linear g (greatCirclePoint u w t) = circle (-r + t) := by
    rw [greatCirclePoint, map_add, map_smul, map_smul, u_frame, w_frame]
    exact greatCirclePoint_complexLift_polarRay (-r) t
  ext x
  constructor
  · intro hx
    have mapped : linear g x ∈ circle '' Set.Icc (-r) r := image_arc ▸ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, eq⟩ := mapped
    refine ⟨t + r, ⟨by linarith [ht.1], by dsimp [r] at *; linarith [ht.2]⟩, ?_⟩
    apply (isometry g).injective
    change linear g (greatCirclePoint u w (t + r)) = linear g x
    rw [map_point, show -r + (t + r) = t by ring]
    exact eq
  · rintro ⟨t, ht, rfl⟩
    have mapped : linear g (greatCirclePoint u w t) ∈ circle '' Set.Icc (-r) r := by
      rw [map_point]
      exact ⟨-r + t, ⟨by linarith [ht.1], by dsimp [r] at *; linarith [ht.2]⟩, rfl⟩
    obtain ⟨y, hy, eq⟩ := image_arc.symm ▸ mapped
    have same : y = greatCirclePoint u w t := (isometry g).injective eq
    exact same ▸ hy

end Unfoldings
