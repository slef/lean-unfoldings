module

public import Unfoldings.FewestNets.AcuteLatitudeBudget
public import Unfoldings.FewestNets.AcuteLatitudeTilt
public import Unfoldings.FewestNets.LatitudeTriangleSelector
public import Unfoldings.Geometry.GraphNormalTilt
public import Unfoldings.Roof.SharpAngleProjection
public import Unfoldings.Roof.Gnomonic

/-! Original-edge three-exit routing for the wider acute latitude triangles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open FewestNets Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C)

set_option maxHeartbeats 1500000 in
/-- The revised chart tilt and side-ratio bounds give a concrete routing of
each selected component. Every root history, including its exit, has
heading width at most `π/2 - 0.170 α`. -/
theorem exists_acuteLatitudeTriangleRouting (seed : Face)
    {a φ left right base apex height : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6)
    (tilt_pos : 0 < φ) (tilt : φ ≤ 0.568 * AcuteLatitudeGrid.radius a)
    (H_low : 0.883 * AcuteLatitudeGrid.radius a < height)
    (B_up : right - left < 1.010 * AcuteLatitudeGrid.spacing a)
    (east : |latitudeEastRatio right apex height| <
      1.144 * AcuteLatitudeGrid.spacing a / AcuteLatitudeGrid.radius a)
    (west : |latitudeWestRatio left apex height| <
      1.144 * AcuteLatitudeGrid.spacing a / AcuteLatitudeGrid.radius a)
    (base_pos : left < right) (height_pos : 0 < height)
    (radius : ∀ p ∈ latitudeSlopeTriangle left right base apex height, ‖p‖ ≤ tan φ)
    (generic : ∀ f, K.normalSlope f ∉ frontier (latitudeSlopeTriangle left right base apex height))
    (selected : K.normalSlope seed ∈ latitudeSlopeTriangle left right base apex height)
    (angles : ∀ f, ∀ i, (C.triangle f).cornerAngle i ≤ π / 2 - a) :
    let B := latitudeTriangleSideDirections left right base apex height base_pos height_pos
    let compact := isCompact_latitudeSlopeTriangle left right base apex height
    let present := Set.nonempty_of_mem selected
    ∃ (H : ThreeExitStemWindows) (R : K.ThreeExitComponentRouting seed B compact present H),
      ∀ r : {r // r ∈ R.stems.choice.parents.roots},
        let exit := (R.rootHeadingChart r (R.rootExitDirection r)).arg
        let lo := R.rootWindowStart r
        max (lo + H.width) exit - min lo exit ≤ π / 2 - 0.170 * a := by
  dsimp only
  let S := latitudeSlopeTriangle left right base apex height
  let B := latitudeTriangleSideDirections left right base apex height base_pos height_pos
  let compact := isCompact_latitudeSlopeTriangle left right base apex height
  let present := Set.nonempty_of_mem selected
  obtain ⟨φ_small, _, cos_pos, projection⟩ := acute_latitude_tilt_budgets
    positive small tilt_pos.le tilt
  have φ_lt : φ < π / 2 := by linarith only [φ_small, pi_gt_three]
  have projected (f : Face) (hf : f ∈ K.selectionComponent S seed) (i : Fin 3) :
      (K.projectedTriangle f).cornerAngle i ≤ π / 2 - 2 * (0.491 * a) := by
    have slope := K.selectionComponent_selected selected hf
    have lower : cos φ ≤ K.normal f 2 := by
      let plane := SpatialPlane.ofGraph 0 (K.normalSlope f)
      have equiv : Cap.gnomonicNormal (K.normalSlope f) = plane.normal := by
        have same : plane.normalSlope = K.normalSlope f := SpatialPlane.ofGraph_normalSlope _ _
        rw [← same]
        exact Cap.gnomonicNormal_slope _ plane.normal_unit plane.normal_upward
      rw [← K.gnomonicNormal_normalSlope f, equiv]
      exact SpatialPlane.ofGraph_normal_height_of_slope_radius tilt_pos φ_lt 0 _ (radius _ slope)
    have allowance := K.projected_cornerAngle_le_of_normal_height cos_pos f lower i (angles f i)
    linarith only [allowance, projection]
  let u := latitudeEastRatio right apex height
  let v := latitudeWestRatio left apex height
  have ratios : v - u = (right - left) / height := by
    dsimp only [u, v, latitudeEastRatio, latitudeWestRatio]
    rw [← sub_div]
    congr 1
    ring
  have ordered : u < v := sub_pos.mp (ratios.symm ▸ div_pos (sub_pos.mpr base_pos) height_pos)
  have r_pos := AcuteLatitudeGrid.radius_pos positive
  have ratio_scale :
      1.144 * AcuteLatitudeGrid.spacing a / AcuteLatitudeGrid.radius a = 0.64064 * a := by
    unfold AcuteLatitudeGrid.spacing
    field_simp [r_pos.ne']
    ring
  have e_bound : |arctan u| ≤ 0.641 * a :=
    abs_arctan_le_abs.trans ((east.le.trans_eq ratio_scale).trans (by linarith only [positive]))
  have w_bound : |arctan v| ≤ 0.641 * a :=
    abs_arctan_le_abs.trans ((west.le.trans_eq ratio_scale).trans (by linarith only [positive]))
  have diff : arctan v - arctan u ≤ v - u := by
    obtain ⟨c, _, slope⟩ := exists_deriv_eq_slope arctan ordered
      continuous_arctan.continuousOn differentiable_arctan.differentiableOn
    rw [Real.deriv_arctan] at slope
    change 1 / (1 + c ^ 2) = (arctan v - arctan u) / (v - u) at slope
    have bound : 1 / (1 + c ^ 2) ≤ 1 :=
      (div_le_one₀ (by positivity)).mpr (by linarith only [sq_nonneg c])
    rw [slope] at bound
    simpa only [one_mul] using (div_le_iff₀ (sub_pos.mpr ordered)).mp bound
  have spread : (right - left) / height < 0.641 * a := by
    apply (div_lt_iff₀ height_pos).mpr
    have scaled := mul_lt_mul_of_pos_left H_low (show 0 < 0.641 * a by positivity)
    unfold AcuteLatitudeGrid.spacing at B_up
    nlinarith only [B_up, scaled, mul_pos positive r_pos]
  have apex_bound : arctan v - arctan u ≤ 0.641 * a := by
    rw [ratios] at diff
    exact diff.trans spread.le
  have margins := acute_latitude_exit_budget positive e_bound w_bound apex_bound
  have first : 0.170 * a < 0.491 * a + arctan u / 2 :=
    margins.trans_le (min_le_left _ _)
  have second : 0.170 * a < 0.491 * a - arctan v / 2 :=
    margins.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have last : 0.170 * a < 2 * (0.491 * a) + arctan u - arctan v := by
    have h : 0.170 * a < 2 * 0.491 * a + arctan u - arctan v :=
      margins.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith only [h]
  have positive_σ : 0 < 0.170 * a := by positivity
  have within : 0.170 * a ≤ 0.491 * a := by linarith only [positive]
  have δ_bound : 0.491 * a ≤ π / 8 := by linarith only [small, pi_pos]
  have acute_width : 0 ≤ π / 2 - 0.170 * a := by linarith only [small, pi_pos]
  have e_arg : (exitHeadingChart false (B.normal 0)).arg = arctan u :=
    latitudeTriangle_east_arg left right base apex height base_pos height_pos
  have w_arg : (exitHeadingChart true (B.normal 1)).arg = -arctan v :=
    latitudeTriangle_west_arg left right base apex height base_pos height_pos
  have n_arg : ∀ b, (exitHeadingChart b (B.normal 2)).arg = π / 2 :=
    latitudeTriangle_north_arg left right base apex height base_pos height_pos
  have e_window : |arctan u| < 2 * (0.491 * a) := by linarith only [e_bound, positive]
  have w_window : |arctan v| < 2 * (0.491 * a) := by linarith only [w_bound, positive]
  obtain ⟨H, ⟨R⟩, r_e, r_w, n_e, n_w⟩ := K.exists_threeExitComponentRouting_of_signed_headings
    seed B compact present positive_σ within δ_bound e_window w_window first second last
    projected e_arg w_arg generic selected
  exact ⟨H, R, R.root_span_of_signed_headings acute_width e_arg w_arg n_arg r_e r_w n_e n_w⟩

end Unfoldings.ConvexRoof
