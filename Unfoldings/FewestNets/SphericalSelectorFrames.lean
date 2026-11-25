module

public import Unfoldings.FewestNets.SphericalSelectorPlacement
public import Unfoldings.FewestNets.SingleCellCentralSets
public import Unfoldings.Geometry.SphericalArcEndpointClip

/-! Centered side parameters and the measurable central crossing events. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.SphericalSelectorBoundary

open SpatialRotation Real InnerProductGeometry MeasureTheory

variable {J : Type*} {region : Set Space}

/-- The centered side parameter has this half-length. -/
def halfLength (B : SphericalSelectorBoundary J region) (j : J) : ℝ :=
  angle (B.endpoint j false) (B.endpoint j true) / 2

theorem halfLength_nonneg (B : SphericalSelectorBoundary J region) (j : J) :
    0 ≤ B.halfLength j :=
  div_nonneg (angle_nonneg _ _) (by norm_num)

namespace MetricData

variable {B : SphericalSelectorBoundary J region} (M : MetricData B)

include M in
theorem side_length_lt_pi (j : J) : angle (B.endpoint j false) (B.endpoint j true) < π := by
  linarith only [M.side_le j, M.longest_small, pi_pos]

include M in
theorem halfLength_small (j : J) : B.halfLength j ≤ π / 2 :=
  div_le_div_of_nonneg_right (M.side_length_lt_pi j).le (by norm_num)

/-- Use the oriented parameter running from the false to the true endpoint. -/
def sideFrame (j : J) : SpatialRotation :=
  (exists_frame_closedMinorArc_with_endpoints (B.endpoint_unit j false) (B.endpoint_unit j true)
    (M.side_pos j) (M.side_length_lt_pi j)).choose

theorem sideFrame_image_arc (j : J) :
    linear (M.sideFrame j) '' equatorialArc (B.halfLength j) = networkEdge B.endpoint j :=
  (exists_frame_closedMinorArc_with_endpoints (B.endpoint_unit j false) (B.endpoint_unit j true)
    (M.side_pos j) (M.side_length_lt_pi j)).choose_spec.1

theorem sideFrame_endpoint (j : J) (b : Bool) :
    linear (M.sideFrame j) (equatorPoint ((arcEndpointPhase (B.halfLength j) b : ℝ) :
      EquatorPhase)) = B.endpoint j b := by
  have h := (exists_frame_closedMinorArc_with_endpoints (B.endpoint_unit j false)
    (B.endpoint_unit j true) (M.side_pos j) (M.side_length_lt_pi j)).choose_spec.2 b
  change linear (M.sideFrame j) (equatorPoint ((arcEndpointPhase (B.halfLength j) b : ℝ) :
    EquatorPhase)) = _ at h
  cases b <;> exact h

/-- A symmetric arc parameter on the stated interval, with its literal endpoints. -/
def sidePoint (j : J) (t : ℝ) : Space :=
  linear (M.sideFrame j) (complexLift (polarRay t))

theorem continuous_sidePoint (j : J) : Continuous (M.sidePoint j) :=
  (isometry (M.sideFrame j)).continuous.comp
    (complexLift.continuous.comp (continuous_subtype_val.comp Circle.exp.continuous))

theorem sidePoint_image (j : J) :
    M.sidePoint j '' Set.Icc (-B.halfLength j) (B.halfLength j) = networkEdge B.endpoint j := by
  rw [← M.sideFrame_image_arc, equatorialArc_eq_image_complexLift
    ((M.halfLength_small j).trans (by linarith only [pi_pos])), Set.image_image]
  rfl

theorem angle_endpoint_sidePoint (j : J) (b : Bool) {t : ℝ}
    (within : t ∈ Set.Icc (-B.halfLength j) (B.halfLength j)) :
    angle (B.endpoint j b) (M.sidePoint j t) =
      if b then B.halfLength j - t else t + B.halfLength j := by
  let r := B.halfLength j
  have small := M.halfLength_small j
  have bounds : -r ≤ t ∧ t ≤ r := within
  rw [← M.sideFrame_endpoint j b, equatorPoint_coe_eq_complexLift]
  change angle ((isometry (M.sideFrame j)).toLinearIsometry _)
    ((isometry (M.sideFrame j)).toLinearIsometry _) = _
  rw [LinearIsometry.angle_map, complexLift.angle_map]
  cases b
  · change angle (polarRay (-r)) (polarRay t) = t + r
    rw [angle_polarRay _ _ (sub_nonneg.mpr bounds.1) (by linarith only [bounds.2, small])]
    ring
  · change angle (polarRay r) (polarRay t) = r - t
    rw [angle_comm, angle_polarRay _ _ (sub_nonneg.mpr bounds.2) (by linarith only [bounds.1, small])]

/-- A placement is central on this side if a point beyond both cutoff
lengths lies in the chosen Gaussian cell. -/
def centralSet (cell : Set Space) (d : ℝ) (b : Bool) (j : J) : Set SpatialRotation :=
  centralOrientations cell (M.sidePoint j)
    (M.endpointFactor j false * d - B.halfLength j)
    (B.halfLength j - M.endpointFactor j true * d) b

theorem measurableSet_centralSet (cell : Set Space) (closed : IsClosed cell)
    (d : ℝ) (b : Bool) (j : J) : MeasurableSet (M.centralSet cell d b j) :=
  centralOrientations_measurable cell closed (M.sidePoint j) (M.continuous_sidePoint j) _ _ b

theorem mem_centralSet_iff (cell : Set Space) {d : ℝ} (nonneg : 0 ≤ d)
    (b : Bool) (j : J) (g : SpatialRotation) :
    g ∈ M.centralSet cell d b j ↔
      ∃ x ∈ networkEdge B.endpoint j, orthogonalIsometry g b x ∈ cell ∧
        ∀ k, M.endpointFactor j k * d < angle (B.endpoint j k) x := by
  let r := B.halfLength j
  have reach (k : Bool) : 0 ≤ M.endpointFactor j k * d :=
    mul_nonneg (M.endpointFactor_pos j k).le nonneg
  constructor
  · rintro ⟨t, ht, contact⟩
    have in_arc : t ∈ Set.Icc (-r) r := ⟨by linarith only [ht.1, reach false],
      by linarith only [ht.2, reach true]⟩
    have x_side : M.sidePoint j t ∈ networkEdge B.endpoint j :=
      (M.sidePoint_image j).subset (Set.mem_image_of_mem _ in_arc)
    refine ⟨_, x_side, by simpa only [orthogonalIsometry_apply] using contact, fun k => ?_⟩
    rw [M.angle_endpoint_sidePoint j k in_arc]
    cases k
    · change M.endpointFactor j false * d < t + r
      linarith only [ht.1]
    · change M.endpointFactor j true * d < r - t
      linarith only [ht.2]
  · rintro ⟨x, on_side, contact, reaches⟩
    rw [← M.sidePoint_image] at on_side
    obtain ⟨t, ht, rfl⟩ := on_side
    have left := reaches false
    have right := reaches true
    rw [M.angle_endpoint_sidePoint j false ht] at left
    rw [M.angle_endpoint_sidePoint j true ht] at right
    refine ⟨t, ⟨?_, ?_⟩, by simpa only [orthogonalIsometry_apply] using contact⟩
    · change M.endpointFactor j false * d - r < t
      change M.endpointFactor j false * d < t + r at left
      linarith only [left]
    · change t < r - M.endpointFactor j true * d
      change M.endpointFactor j true * d < r - t at right
      linarith only [right]

end MetricData
end Unfoldings.FewestNets.SphericalSelectorBoundary
