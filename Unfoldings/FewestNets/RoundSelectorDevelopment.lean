module

public import Unfoldings.FewestNets.RoundSelectorRouting
public import Unfoldings.FewestNets.AcuteSelectorThreshold
public import Unfoldings.Roof.SharpAngleProjection
public import Unfoldings.Geometry.GraphNormalTilt
public import Unfoldings.Roof.PolygonClippedModel
public import Unfoldings.Roof.AdaptiveComponentDevelopment

/-! The polar selector theorem at the actual squared tilt and on original seams. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real FewestNets

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C)

set_option maxHeartbeats 1200000 in
/-- A round polar polygon whose apothem is the circumradius times cos x
unfolds all selected components on original seams. The rotation avoids
putting an original face normal on the polygon boundary. -/
theorem hasOriginalEdgeNet_of_roundSelector_of_aperture {I : Type} [Fintype I] [Nonempty I]
    {slopes : Set Plane} (B : PolygonSideDirections I slopes)
    {a phi x : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (tilt_pos : 0 < phi) (tilt_sq : phi ^ 2 ≤ a / 144)
    (x_nonneg : 0 ≤ x) (x_upper : x ≤ π / 6)
    (aperture : 1 / (√2 * cos x) < cos (π / 4 - 0.49 * a))
    (exit_margin : 0.48 * a ≤ cos (π / 4 + x))
    (side_distance : ∀ i, B.offset i = tan phi * cos x)
    (radius_bound : ∀ p ∈ slopes, ‖p‖ ≤ tan phi)
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
    (angles : ∀ f, ∀ i, (C.triangle f).cornerAngle i ≤ π / 2 - a) :
    ∀ seed, K.normalSlope seed ∈ slopes → C.HasOriginalEdgeNet (K.selectionComponent slopes seed) := by
  have a_upper : a ≤ 0.524 := by linarith only [small, pi_lt_d4]
  have phi_lower : phi ≤ 1 / 10 := by
    by_contra! h
    have sq := pow_lt_pow_left₀ h (by norm_num : (0 : ℝ) ≤ 1 / 10)
      (by decide : (2 : ℕ) ≠ 0)
    linarith only [sq, tilt_sq, a_upper]
  have phi_small : phi < π / 2 := by linarith only [phi_lower, pi_gt_d2]
  have cos_lower : 3 / 4 ≤ cos phi := by
    linarith only [one_sub_sq_div_two_le_cos (x := phi), tilt_sq, a_upper]
  have cos_pos : 0 < cos phi := by linarith only [cos_lower]
  have radius_pos : 0 < tan phi := by
    rw [tan_eq_sin_div_cos]
    exact div_pos (sin_pos_of_pos_of_lt_pi tilt_pos (by linarith only [phi_small, pi_pos])) cos_pos
  have disk : slopes ⊆ Metric.closedBall 0 (tan phi) := fun p hp => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using radius_bound p hp
  let compact := (isCompact_closedBall (0 : Plane) (tan phi)).of_isClosed_subset B.isClosed disk
  let present : slopes.Nonempty := ⟨B.reference, interior_subset B.reference_mem_interior⟩
  let boundary : (frontier slopes).Nonempty := nonempty_frontier_iff.mpr
    ⟨present, fun equal => NormedSpace.unbounded_univ ℝ Plane (equal ▸ compact.isBounded)⟩
  obtain ⟨M⟩ := K.exists_finiteSlopeModel_of_polygon B compact present
  have normal (i : M.Face) : cos phi ≤ (M.plane i).normal 2 :=
    SpatialPlane.ofGraph_normal_height_of_slope_radius tilt_pos phi_small _ _
      (radius_bound _ (M.included i.val i.property))
  have projected (f : Face) (hf : K.normalSlope f ∈ slopes) (i : Fin 3) :
      (K.projectedTriangle f).cornerAngle i ≤ π / 2 - 0.99 * a := by
    have height : cos phi ≤ K.normal f 2 := by
      let plane := SpatialPlane.ofGraph 0 (K.normalSlope f)
      have equiv : Cap.gnomonicNormal (K.normalSlope f) = plane.normal := by
        have slope : plane.normalSlope = K.normalSlope f := SpatialPlane.ofGraph_normalSlope _ _
        rw [← slope]
        exact Cap.gnomonicNormal_slope _ plane.normal_unit plane.normal_upward
      rw [← K.gnomonicNormal_normalSlope f, equiv]
      exact SpatialPlane.ofGraph_normal_height_of_slope_radius tilt_pos phi_small 0 _
        (radius_bound _ hf)
    have local_bound := K.projected_cornerAngle_le_of_normal_height cos_pos f height i (angles f i)
    have allowance := projection_allowance_le_sq tilt_pos.le phi_lower
    linarith only [local_bound, allowance, tilt_sq, positive]
  obtain ⟨routing⟩ := K.exists_roundSelectorRouting_of_aperture B compact present boundary no_boundary
    positive small x_nonneg x_upper aperture exit_margin radius_pos side_distance radius_bound projected
  let progress := tan phi / √(2 : ℝ)
  let gamma := 0.48 * a
  have root_pos : 0 < √(2 : ℝ) := by positivity
  have root_le : 1 ≤ √(2 : ℝ) := (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have progression : 0 < progress := div_pos radius_pos root_pos
  have ratio : progress ≤ tan phi := div_le_self radius_pos.le root_le
  have length : tan phi / progress ≤ √2 := by
    change tan phi / (tan phi / √(2 : ℝ)) ≤ _
    rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ radius_pos.ne']
  have gamma_pos : 0 < gamma := by dsimp only [gamma]; positivity
  have zero_mesh : (0 : ℝ) ^ 2 ≤ a / 4 := by
    norm_num
    positivity
  obtain ⟨inside_margin, _, gamma_bound⟩ :=
    round_selector_margin (x := 0) positive small le_rfl zero_mesh
  have flat : phi ^ 2 ≤ gamma / 58 := by
    dsimp only [gamma]
    linarith only [tilt_sq, positive]
  have E := (sharp_polar_development_threshold gamma_pos gamma_bound tilt_pos.le flat
    (sqrt_nonneg 2) (le_refl (√(2 : ℝ)))).1
  exact K.hasOriginalEdgeNet_of_adaptiveRouting B.convex compact present routing no_boundary M
    progression Set.Subset.rfl radius_pos ratio radius_bound tilt_pos phi_small cos_lower normal
    gamma_pos (gamma_bound.trans (by norm_num)) inside_margin le_rfl length E

/-- The original small-step criterion for an original-edge net in each selected component. -/
theorem hasOriginalEdgeNet_of_roundSelector {I : Type} [Fintype I] [Nonempty I]
    {slopes : Set Plane} (B : PolygonSideDirections I slopes)
    {a phi x : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (tilt_pos : 0 < phi) (tilt_sq : phi ^ 2 ≤ a / 144)
    (x_nonneg : 0 ≤ x) (mesh : x ^ 2 ≤ a / 4)
    (side_distance : ∀ i, B.offset i = tan phi * cos x)
    (radius_bound : ∀ p ∈ slopes, ‖p‖ ≤ tan phi)
    (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
    (angles : ∀ f, ∀ i, (C.triangle f).cornerAngle i ≤ π / 2 - a) :
    ∀ seed, K.normalSlope seed ∈ slopes → C.HasOriginalEdgeNet (K.selectionComponent slopes seed) := by
  obtain ⟨x_upper, aperture, exit_margin⟩ := roundSelector_aperture_of_small_step positive small x_nonneg mesh
  exact K.hasOriginalEdgeNet_of_roundSelector_of_aperture B positive small tilt_pos tilt_sq
    x_nonneg x_upper aperture exit_margin side_distance radius_bound no_boundary angles

end Unfoldings.ConvexRoof
