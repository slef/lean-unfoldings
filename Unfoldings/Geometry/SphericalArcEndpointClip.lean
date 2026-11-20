module

public import Unfoldings.Geometry.MinorArcArclength

/-! End portions of a framed arc have explicit Crofton frames and bounded length. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialRotation

open InnerProductGeometry Real

/-- Endpoint phases of an arc of half-length `r` about the zero phase. -/
def arcEndpointPhase (r : ℝ) (side : Bool) : ℝ :=
  if side then r else -r

/-- The endpoint portion has length at most the requested reach and the whole arc length. -/
def endpointClipRadius (r reach : ℝ) : ℝ := min r (reach / 2)

/-- Move the midpoint of a Crofton frame to the center of the chosen endpoint portion. -/
def endpointClipFrame (g : SpatialRotation) (r reach : ℝ) (side : Bool) : SpatialRotation :=
  g * phaseRotation ((arcEndpointPhase (r - endpointClipRadius r reach) side : ℝ) : EquatorPhase)

theorem endpointClipRadius_nonneg {r reach : ℝ} (hr : 0 ≤ r) (reach_nonneg : 0 ≤ reach) :
    0 ≤ endpointClipRadius r reach := le_min hr (by positivity)

theorem two_mul_endpointClipRadius_le (r reach : ℝ) :
    2 * endpointClipRadius r reach ≤ reach := by
  unfold endpointClipRadius
  linarith only [min_le_right r (reach / 2)]

/-- A point on the framed arc within the requested angular reach of an
endpoint lies in that endpoint's Crofton arc. -/
theorem mem_endpointClip_of_angle_le {g : SpatialRotation} {r reach : ℝ}
    (hr : 0 ≤ r) (short : r ≤ π / 2) (reach_nonneg : 0 ≤ reach)
    {side : Bool} {x : Space} (on_arc : x ∈ linear g '' equatorialArc r)
    (close : angle (linear g (equatorPoint ((arcEndpointPhase r side : ℝ) : EquatorPhase))) x ≤
      reach) :
    x ∈ linear (endpointClipFrame g r reach side) ''
      equatorialArc (endpointClipRadius r reach) := by
  obtain ⟨_, y_arc, rfl⟩ := on_arc
  rw [equatorialArc_eq_image_complexLift (by linarith [pi_pos])] at y_arc
  obtain ⟨t, ht, rfl⟩ := y_arc
  have angle_eq : angle (linear g (equatorPoint ((arcEndpointPhase r side : ℝ) : EquatorPhase)))
      (linear g (complexLift (polarRay t))) = if side then r - t else t + r := by
    change angle ((isometry g).toLinearIsometry _) ((isometry g).toLinearIsometry _) = _
    rw [(isometry g).toLinearIsometry.angle_map, equatorPoint_coe_eq_complexLift,
      complexLift.angle_map]
    cases side
    · change angle (polarRay (-r)) (polarRay t) = t + r
      rw [angle_polarRay _ _ (by linarith [ht.1]) (by linarith [ht.2])]
      ring
    · change angle (polarRay r) (polarRay t) = r - t
      rw [angle_comm, angle_polarRay _ _ (by linarith [ht.2]) (by linarith [ht.1])]
  rw [angle_eq] at close
  let h := endpointClipRadius r reach
  let center := arcEndpointPhase (r - h) side
  have h_nonneg : 0 ≤ h := endpointClipRadius_nonneg hr reach_nonneg
  have h_le : h ≤ r := min_le_left _ _
  have inside : t - center ∈ Set.Icc (-h) h := by
    by_cases radius : r ≤ reach / 2
    · have eq : h = r := min_eq_left radius
      have zero : center = 0 := by simp [center, eq, arcEndpointPhase]
      simpa only [zero, sub_zero, eq] using ht
    · have eq : h = reach / 2 := min_eq_right (le_of_not_ge radius)
      cases side
      · change t + r ≤ reach at close
        change -(h : ℝ) ≤ t - (-(r - h)) ∧ t - (-(r - h)) ≤ h
        exact ⟨by linarith [ht.1], by linarith [eq]⟩
      · change r - t ≤ reach at close
        change -(h : ℝ) ≤ t - (r - h) ∧ t - (r - h) ≤ h
        exact ⟨by linarith [eq], by linarith [ht.2]⟩
  have phase_ball : ((t - center : ℝ) : EquatorPhase) ∈ Metric.closedBall 0 h :=
    (equatorPhase_mem_closedBall_iff ((abs_le.mpr inside).trans (by linarith [pi_pos]))).mpr inside
  refine ⟨equatorPoint ((t - center : ℝ) : EquatorPhase), ⟨_, phase_ball, rfl⟩, ?_⟩
  rw [endpointClipFrame, linear_mul, LinearMap.comp_apply, linear_phaseRotation_equatorPoint]
  change linear g (equatorPoint ((center : EquatorPhase) + ((t - center : ℝ) : EquatorPhase))) = _
  have sum : center + (t - center) = t := by ring
  rw [← AddCircle.coe_add, sum, equatorPoint_coe_eq_complexLift]

/-- A centered frame identifies both endpoints of the actual closed arc. -/
theorem exists_frame_closedMinorArc_with_endpoints {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (positive : 0 < angle u v) (small : angle u v < π) :
    ∃ g : SpatialRotation,
      linear g '' equatorialArc (angle u v / 2) = closedMinorArc u v ∧
      ∀ side : Bool, linear g (equatorPoint
        ((arcEndpointPhase (angle u v / 2) side : ℝ) : EquatorPhase)) = if side then v else u := by
  obtain ⟨g, left, right⟩ := exists_centered_arc_rotation hu hv
  refine ⟨g⁻¹, ?_, ?_⟩
  · have arc := equatorialArc_eq_closedMinorArc (r := angle u v / 2) (by positivity) (by linarith)
    rw [← left, ← right] at arc
    rw [arc, image_closedMinorArc, linear_inv_apply, linear_inv_apply]
  · intro side
    cases side
    · change linear g⁻¹ (equatorPoint ((-(angle u v / 2) : ℝ) : EquatorPhase)) = u
      rw [← left, linear_inv_apply]
    · change linear g⁻¹ (equatorPoint ((angle u v / 2 : ℝ) : EquatorPhase)) = v
      rw [← right, linear_inv_apply]

end Unfoldings.SpatialRotation
