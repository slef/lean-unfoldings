module

public import Unfoldings.FewestNets.LatitudeTriangleSelector
public import Unfoldings.FewestNets.RoundSelectorDevelopment

/-! A latitude triangle at the paper's scale admits the exact original-edge three-exit routing. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open FewestNets Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (K : ConvexRoof C)

set_option maxHeartbeats 1500000 in
-- The component, its original cuts and the projected cell all use the same chart.
/-- The latitude base, height and long-side estimates leave enough room for
the original-edge parents and keep their full root cones strictly acute. -/
theorem exists_latitudeTriangleRouting (seed : Face)
    {a φ r b left right base apex height : ℝ}
    (positive : 0 < a) (small : a ≤ π / 6)
    (tilt_pos : 0 < φ) (tilt : φ ≤ 0.0848 * √a)
    (r_pos : 0 < r) (spacing : b = 0.45 * a * r) (b_small : b < 0.236 * r)
    (H_low : 0.93 * r < height) (H_up : height < 1.032 * r)
    (B_low : 0.92 * b < right - left) (B_up : right - left < 1.01 * b)
    (east : |latitudeEastRatio right apex height| < 1.08 * b / r)
    (west : |latitudeWestRatio left apex height| < 1.08 * b / r)
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
        max (lo + H.width) exit - min lo exit ≤ π / 2 - 0.235 * a := by
  dsimp only
  let S := latitudeSlopeTriangle left right base apex height
  let B := latitudeTriangleSideDirections left right base apex height base_pos height_pos
  let compact := isCompact_latitudeSlopeTriangle left right base apex height
  let present := Set.nonempty_of_mem selected
  have a_le : a ≤ 1 := by linarith only [small, pi_lt_d4]
  have sqrt_le : √a ≤ 1 := by simpa only [sqrt_one] using sqrt_le_sqrt a_le
  have φ_small : φ < π / 2 := by
    have cap := mul_le_mul_of_nonneg_left sqrt_le (by norm_num : (0 : ℝ) ≤ 0.0848)
    linarith only [tilt, cap, pi_gt_three]
  obtain ⟨cos_pos, projection, _, _, _⟩ := latitude_three_exit_tilt_bounds
    positive small tilt_pos.le tilt
  have projected (f : Face) (hf : f ∈ K.selectionComponent S seed) (i : Fin 3) :
      (K.projectedTriangle f).cornerAngle i ≤ π / 2 - 2 * (0.495 * a) := by
    have slope := K.selectionComponent_selected selected hf
    have lower : cos φ ≤ K.normal f 2 := by
      let plane := SpatialPlane.ofGraph 0 (K.normalSlope f)
      have equiv : Cap.gnomonicNormal (K.normalSlope f) = plane.normal := by
        have same : plane.normalSlope = K.normalSlope f := SpatialPlane.ofGraph_normalSlope _ _
        rw [← same]
        exact Cap.gnomonicNormal_slope _ plane.normal_unit plane.normal_upward
      rw [← K.gnomonicNormal_normalSlope f, equiv]
      exact SpatialPlane.ofGraph_normal_height_of_slope_radius tilt_pos φ_small 0 _
        (radius _ slope)
    have allowance := K.projected_cornerAngle_le_of_normal_height cos_pos f lower i (angles f i)
    linarith only [allowance, projection]
  let u := latitudeEastRatio right apex height
  let v := latitudeWestRatio left apex height
  have ratios : v - u = (right - left) / height := by
    dsimp only [u, v, latitudeEastRatio, latitudeWestRatio]
    rw [← sub_div]
    congr 1
    ring
  obtain ⟨em, wm, el, wl, both, _⟩ := latitude_exit_margins_of_side_ratios
    positive r_pos spacing b_small H_low H_up B_low B_up east west ratios
  have positive_σ : 0 < 0.235 * a := by positivity
  have within : 0.235 * a ≤ 0.495 * a := by linarith only [positive]
  have δ_bound : 0.495 * a ≤ π / 8 := by linarith only [small, pi_pos]
  have acute_width : 0 ≤ π / 2 - 0.235 * a := by linarith only [small, pi_pos]
  have e_arg : (exitHeadingChart false (B.normal 0)).arg = arctan u :=
    latitudeTriangle_east_arg left right base apex height base_pos height_pos
  have w_arg : (exitHeadingChart true (B.normal 1)).arg = -arctan v :=
    latitudeTriangle_west_arg left right base apex height base_pos height_pos
  have n_arg : ∀ b, (exitHeadingChart b (B.normal 2)).arg = π / 2 :=
    latitudeTriangle_north_arg left right base apex height base_pos height_pos
  have e_window : |arctan u| < 2 * (0.495 * a) := by linarith only [em]
  have w_window : |arctan v| < 2 * (0.495 * a) := by linarith only [wm]
  have width : 0.235 * a < 2 * (0.495 * a) + arctan u - arctan v := by
    linarith only [both]
  obtain ⟨H, ⟨R⟩, r_e, r_w, n_e, n_w⟩ := K.exists_threeExitComponentRouting_of_signed_headings
    seed B compact present positive_σ within δ_bound e_window w_window el wl width
    projected e_arg w_arg generic selected
  exact ⟨H, R, R.root_span_of_signed_headings acute_width e_arg w_arg n_arg r_e r_w n_e n_w⟩

end Unfoldings.ConvexRoof
