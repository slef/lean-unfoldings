module

public import Unfoldings.FewestNets.RevisedLatitudeSelectors
public import Unfoldings.FewestNets.RevisedLatitudeBaseSampling
public import Unfoldings.Geometry.RegularPolygonMetric
public import Unfoldings.Geometry.GnomonicMinorArc
public import Unfoldings.Geometry.GnomonicDistanceBounds
public import Unfoldings.Geometry.GnomonicCornerAngles
public import Unfoldings.FewestNets.AcuteLatitudeCornerScalars

/-! The two actual polar cells have short sides, wide corners, and separated nonincident sides. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Cap Real InnerProductGeometry
open AcuteLatitudeGrid (polarFrame polarRadius polarRadius_pos polarRadius_lt)

theorem polar_rows_ge_six {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    6 ≤ rowSize a 0 := by
  rw [(rowSize_at_poles (a := a)).1]
  exact (polarSize_bounds positive small).1

/-- The actual ring vertex in either polar chart. -/
def polarSlopeVertex (a : ℝ) (j : ℕ) : Plane :=
  regularRingVertex polarFrame (rowSize a 0) (tan (polarRadius a)) j

/-- Each closed polar side in the original placed sphere. -/
def polarSide {a : ℝ} (pole : Fin 2) (i : Fin (rowSize a 0)) : Set Space :=
  selectorFrame (a := a) (.inl pole) ⁻¹'
    (gnomonicNormal '' segment ℝ (polarSlopeVertex a i.val) (polarSlopeVertex a (i.val + 1)))

/-- The intrinsic spherical side length in either polar chart. -/
def polarSideLength {a : ℝ} (i : Fin (rowSize a 0)) : ℝ :=
  angle (gnomonicNormal (polarSlopeVertex a i.val))
    (gnomonicNormal (polarSlopeVertex a (i.val + 1)))

/-- The actual perimeter of each polar polygon. -/
def polarPerimeter (a : ℝ) : ℝ := ∑ i : Fin (rowSize a 0), polarSideLength i

/-- The angle at the terminal vertex of the indicated side, measured between the
two inward-going tangents in the polar chart. -/
def polarCornerAngle {a : ℝ} (i : Fin (rowSize a 0)) : ℝ :=
  let p := gnomonicNormal (polarSlopeVertex a (i.val + 1))
  let q := gnomonicNormal (polarSlopeVertex a i.val)
  let r := gnomonicNormal (polarSlopeVertex a (i.val + 2))
  angle (minorArcTangent p q) (minorArcTangent p r)

private theorem polarRadius_cos_gt {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    (0.998 : ℝ) < cos (polarRadius a) := by
  have radius := polarRadius_lt small
  have sum : 0 < 0.061 + polarRadius a := by linarith [polarRadius_pos positive]
  have square : polarRadius a ^ 2 < (0.061 : ℝ) ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr radius) sum]
  nlinarith only [square, one_sub_sq_div_two_le_cos (x := polarRadius a)]

theorem tan_polarRadius_bounds {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    0 < tan (polarRadius a) ∧ tan (polarRadius a) < 0.062 := by
  have h := polarRadius_pos positive
  have upper := polarRadius_lt small
  have cosine := polarRadius_cos_gt positive small
  refine ⟨tan_pos_of_pos_of_lt_pi_div_two h (by linarith only [upper, pi_gt_d2]), ?_⟩
  rw [tan_eq_sin_div_cos]
  exact (div_lt_iff₀ (by linarith only [cosine])).mpr
    (by linarith only [sin_le h.le, upper, cosine])

theorem polarSlopeVertex_norm {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) (j : ℕ) :
    ‖polarSlopeVertex a j‖ = tan (polarRadius a) := by
  simp only [polarSlopeVertex, regularRingVertex, norm_smul, Real.norm_eq_abs,
    abs_of_pos (tan_polarRadius_bounds positive small).1, polarFrame.symm.norm_map,
    norm_polarRay, mul_one]

theorem polarSlopeVertex_gnomonic {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) (j : ℕ) :
    gnomonicNormal (polarSlopeVertex a j) = (rings a).rowSite 0 j := by
  rw [show polarSlopeVertex a j = _ from (north_row_gnomonic a j).symm]
  apply gnomonicNormal_slope
  · exact latitudeSite_unit _ _
  · have bound := polarRadius_cos_gt positive small
    change 0 < cos (colatitude a 0)
    simpa only [colatitude, Nat.cast_zero, zero_mul, add_zero] using
      (by linarith only [bound] : 0 < cos (polarRadius a))

private theorem gnomonic_polar_height_ge {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (p : Plane) (near : ‖p‖ ≤ tan (polarRadius a)) :
    cos (polarRadius a) ≤ gnomonicNormal p 2 := by
  let q := polarSlopeVertex a 0
  have q_norm : ‖q‖ = tan (polarRadius a) := polarSlopeVertex_norm positive small 0
  have norm_sq (z : Plane) : ‖northLift z‖ ^ 2 = ‖z‖ ^ 2 + 1 := by
    rw [horizontal_norm_sq, northLift_horizontal, northLift_height, one_pow]
  have shorter : ‖northLift p‖ ≤ ‖northLift q‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq, norm_sq, q_norm]
    linarith only [pow_le_pow_left₀ (norm_nonneg p) near 2]
  have height (z : Plane) : gnomonicNormal z 2 = ‖northLift z‖⁻¹ := by
    change ‖northLift z‖⁻¹ * 1 = _
    rw [mul_one]
  have reference : gnomonicNormal q 2 = cos (polarRadius a) := by
    dsimp only [q]
    rw [polarSlopeVertex_gnomonic positive small]
    change cos (colatitude a 0) = _
    simp only [colatitude, Nat.cast_zero, zero_mul, add_zero]
  rw [← reference, height, height]
  exact (inv_le_inv₀ (norm_pos_iff.mpr (northLift_ne_zero q))
    (norm_pos_iff.mpr (northLift_ne_zero p))).mpr shorter

private theorem norm_le_of_mem_polarSlopeSide {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : ℕ) {z : Plane}
    (member : z ∈ segment ℝ (polarSlopeVertex a i) (polarSlopeVertex a (i + 1))) :
    ‖z‖ ≤ tan (polarRadius a) := by
  have boundary (j : ℕ) : polarSlopeVertex a j ∈ Metric.closedBall (0 : Plane) (tan (polarRadius a)) := by
    rw [Metric.mem_closedBall, dist_zero_right, polarSlopeVertex_norm positive small]
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (convex_closedBall (0 : Plane) (tan (polarRadius a))).segment_subset (boundary i)
      (boundary (i + 1)) member

/-- In its prescribed chart, the actual spherical side is the minor great-circle arc. -/
theorem polarSide_chart {a : ℝ} (pole : Fin 2) (i : Fin (rowSize a 0)) :
    selectorFrame (a := a) (.inl pole) '' polarSide pole i =
      closedMinorArc (gnomonicNormal (polarSlopeVertex a i.val))
        (gnomonicNormal (polarSlopeVertex a (i.val + 1))) := by
  rw [← gnomonicNormal_image_segment]
  apply Set.image_preimage_eq
  exact (selectorFrame (a := a) (.inl pole)).surjective

/-- The planar ring distance bounds each spherical side length. -/
theorem polarSideLength_le {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (j : Fin (rowSize a 0)) :
    polarSideLength j ≤ 2 * tan (polarRadius a) * sin (π / (rowSize a 0 : ℝ)) := by
  have chord := regularRingVertex_dist_succ polarFrame (polar_rows_ge_six positive small)
    j.val (tan_polarRadius_bounds positive small).1.le
  exact (angle_gnomonicNormal_le_dist _ _).trans_eq chord

theorem polarSideLength_lt {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (j : Fin (rowSize a 0)) : polarSideLength j < 0.124 := by
  have R_pos := (tan_polarRadius_bounds positive small).1
  have h := (polarSideLength_le positive small j).trans
    (mul_le_of_le_one_right (mul_nonneg (by norm_num) R_pos.le) (sin_le_one _))
  linarith only [h, (tan_polarRadius_bounds positive small).2]

theorem polarPerimeter_le {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    polarPerimeter a ≤ 2 * π * tan (polarRadius a) := by
  let k := rowSize a 0
  have k_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr (rowSize_pos positive small (Nat.zero_le _))
  have radius := (tan_polarRadius_bounds positive small).1
  have per_side (j : Fin k) : polarSideLength j ≤ 2 * tan (polarRadius a) * (π / (k : ℝ)) :=
    (polarSideLength_le positive small j).trans
      (mul_le_mul_of_nonneg_left (sin_le (div_nonneg pi_pos.le k_pos.le)) (by positivity))
  calc
    polarPerimeter a ≤ ∑ _ : Fin k, 2 * tan (polarRadius a) * (π / (k : ℝ)) :=
      Finset.sum_le_sum (fun j _ => per_side j)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [k_pos.ne']

/-- The paper's nonincident-side cutoff for each actual polar cell. -/
def polarSideCutoff (a : ℝ) : ℝ := 4 * tan (polarRadius a) / (rowSize a 0 : ℝ)

theorem polarSideCutoff_bounds {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    0 < polarSideCutoff a ∧ polarSideCutoff a < 1 / 10 := by
  have enough := (polar_rows_ge_six positive small)
  have k_ge : (6 : ℝ) ≤ rowSize a 0 := by exact_mod_cast enough
  have k_pos : 0 < (rowSize a 0 : ℝ) := by linarith only [k_ge]
  obtain ⟨radius, upper⟩ := tan_polarRadius_bounds positive small
  exact ⟨div_pos (by positivity) k_pos, (div_lt_iff₀ k_pos).mpr (by linarith only [upper, k_ge])⟩

set_option maxHeartbeats 1000000 in
-- The planar side distance and the inverse chart use the same ring vertices.
/-- With the two sides in cyclic order, their nonincident separation is at least
the cutoff, measured in the original sphere for either pole. -/
theorem polarSideCutoff_le_angle_of_nonincident {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (pole : Fin 2) (i j : Fin (rowSize a 0)) (before : i.val + 2 ≤ j.val)
    (after : j.val + 2 ≤ i.val + rowSize a 0) {x y : Space}
    (on_first : x ∈ polarSide pole i) (on_last : y ∈ polarSide pole j) :
    polarSideCutoff a ≤ angle x y := by
  let k := rowSize a 0
  let R := tan (polarRadius a)
  let ρ := polarRadius a
  obtain ⟨p, pp, x_position⟩ := on_first
  obtain ⟨q, qq, y_position⟩ := on_last
  have enough := (polar_rows_ge_six positive small)
  have radius : 0 < R := (tan_polarRadius_bounds positive small).1
  have planar : 2 * R * sin (π / (k : ℝ)) ≤ dist p q :=
    regularRingSide_dist_ge polarFrame enough before after radius.le pp qq
  have cos_large := polarRadius_cos_gt positive small
  have cos_pos : 0 < cos ρ := by linarith only [cos_large]
  have estimate := dist_le_inv_sq_mul_gnomonicAngle p q cos_pos (cos_le_one ρ)
    (gnomonic_polar_height_ge positive small p (norm_le_of_mem_polarSlopeSide positive small i.val pp))
    (gnomonic_polar_height_ge positive small q (norm_le_of_mem_polarSlopeSide positive small j.val qq))
  have scaled : cos ρ ^ 2 * dist p q ≤ angle x y := by
    have h := mul_le_mul_of_nonneg_left estimate (sq_nonneg (cos ρ))
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ cos_pos.ne'), one_mul,
      x_position, y_position] at h
    exact h.trans_eq ((selectorFrame (.inl pole : Selector a)).toLinearIsometry.angle_map x y)
  have k_ge : (6 : ℝ) ≤ k := by exact_mod_cast enough
  have k_pos : 0 < (k : ℝ) := by linarith only [k_ge]
  let t := 6 / (k : ℝ)
  have tn : 0 ≤ t := by dsimp [t]; positivity
  have tl : t ≤ 1 := (div_le_one k_pos).mpr k_ge
  have chord := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 π from ⟨le_rfl, pi_pos.le⟩)
    (show π / 6 ∈ Set.Icc (0 : ℝ) π from ⟨by positivity, by linarith only [pi_pos]⟩)
    (sub_nonneg.mpr tl) tn (sub_add_cancel 1 t)
  simp only [smul_eq_mul, mul_zero, zero_add, sin_zero, sin_pi_div_six] at chord
  have sine : 3 / (k : ℝ) ≤ sin (π / (k : ℝ)) := by
    convert chord using 2 <;> dsimp only [t] <;> ring
  have cos_sq : (2 / 3 : ℝ) ≤ cos ρ ^ 2 := by
    change (2 / 3 : ℝ) ≤ cos (polarRadius a) ^ 2
    nlinarith only [cos_large, sq_nonneg (cos (polarRadius a) - 0.998)]
  calc
    polarSideCutoff a = (2 / 3) * (2 * R * (3 / (k : ℝ))) := by
      change 4 * R / (k : ℝ) = _
      ring
    _ ≤ cos ρ ^ 2 * (2 * R * sin (π / (k : ℝ))) :=
      mul_le_mul cos_sq (mul_le_mul_of_nonneg_left sine (by positivity)) (by positivity) (sq_nonneg _)
    _ ≤ cos ρ ^ 2 * dist p q := mul_le_mul_of_nonneg_left planar (sq_nonneg _)
    _ ≤ angle x y := scaled

private theorem polar_step_bounds {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    0 < π / (rowSize a 0 : ℝ) ∧ π / (rowSize a 0 : ℝ) ≤ π / 6 := by
  have enough := (polar_rows_ge_six positive small)
  have lower : (6 : ℝ) ≤ rowSize a 0 := by exact_mod_cast enough
  exact ⟨div_pos pi_pos (by linarith only [lower]),
    div_le_div_of_nonneg_left pi_pos.le (by norm_num) lower⟩

private theorem adjacent_polarSlopeVertex_ne {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (j : ℕ) : polarSlopeVertex a j ≠ polarSlopeVertex a (j + 1) := by
  have chord := regularRingVertex_dist_succ polarFrame (polar_rows_ge_six positive small) j
    (tan_polarRadius_bounds positive small).1.le
  obtain ⟨x_pos, x_le⟩ := polar_step_bounds positive small
  have sine := sin_pos_of_pos_of_lt_pi x_pos (by linarith only [x_le, pi_pos])
  have length : 0 < dist (polarSlopeVertex a j) (polarSlopeVertex a (j + 1)) :=
    chord.symm ▸ (mul_pos (mul_pos (by norm_num) (tan_polarRadius_bounds positive small).1) sine)
  exact dist_pos.mp length

theorem polarSideLength_pos {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : Fin (rowSize a 0)) : 0 < polarSideLength i := by
  let p := polarSlopeVertex a i.val
  let q := polarSlopeVertex a (i.val + 1)
  have cos_pos : 0 < cos (polarRadius a) := by linarith [polarRadius_cos_gt positive small]
  have estimate := dist_le_inv_sq_mul_gnomonicAngle p q cos_pos (cos_le_one _)
    (gnomonic_polar_height_ge positive small p (polarSlopeVertex_norm positive small i.val).le)
    (gnomonic_polar_height_ge positive small q (polarSlopeVertex_norm positive small (i.val + 1)).le)
  change 0 < angle (gnomonicNormal p) (gnomonicNormal q)
  refine lt_of_le_of_ne (angle_nonneg _ _) (fun zero => ?_)
  rw [← zero, mul_zero] at estimate
  exact (not_lt_of_ge estimate) (dist_pos.mpr (adjacent_polarSlopeVertex_ne positive small i.val))

/-- The actual spherical corner has half-angle sine greater than one half. -/
theorem polar_corner_halfSine_gt {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : Fin (rowSize a 0)) : 0.7984 ≤ sin (polarCornerAngle i / 2) := by
  let p := polarSlopeVertex a (i.val + 1)
  let q := polarSlopeVertex a i.val
  let r := polarSlopeVertex a (i.val + 2)
  have bound := sin_half_gnomonic_corner_ge p q r
    (adjacent_polarSlopeVertex_ne positive small i.val)
    (adjacent_polarSlopeVertex_ne positive small (i.val + 1)).symm
  have planar : sin (angle (q - p) (r - p) / 2) = cos (π / (rowSize a 0 : ℝ)) :=
    regularRingCorner_half_sine polarFrame (polar_rows_ge_six positive small) i.val
      (tan_polarRadius_bounds positive small).1
  rw [planar] at bound
  obtain ⟨step_pos, step_le⟩ := polar_step_bounds positive small
  have step_cos : (0.8 : ℝ) < cos (π / (rowSize a 0 : ℝ)) := by
    have lower := cos_le_cos_of_nonneg_of_le_pi step_pos.le
      (by linarith only [pi_pos] : π / 6 ≤ π) step_le
    rw [cos_pi_div_six] at lower
    have root : (1.6 : ℝ) < √3 := by
      apply (sq_lt_sq₀ (by norm_num) (sqrt_nonneg _)).mp
      rw [sq_sqrt (by norm_num)]
      norm_num
    linarith only [lower, root]
  have p_height := gnomonic_polar_height_ge positive small p
    (polarSlopeVertex_norm positive small (i.val + 1)).le
  have height_lower : (0.998 : ℝ) ≤ gnomonicNormal p 2 :=
    (polarRadius_cos_gt positive small).le.trans p_height
  have product := mul_le_mul height_lower step_cos.le (by norm_num : (0 : ℝ) ≤ 0.8)
    (gnomonicNormal_upward p).le
  exact (show (0.7984 : ℝ) ≤ 0.998 * 0.8 by norm_num).trans (product.trans bound)

theorem polar_corner_capped_sine {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6)
    (i : Fin (rowSize a 0)) : sin (min (polarCornerAngle i) (π / 2)) = 1 := by
  have nonnegative : 0 ≤ polarCornerAngle i := angle_nonneg _ _
  have below : sin (π / 4) < (0.7984 : ℝ) := by
    rw [sin_pi_div_four]
    have root : √(2 : ℝ) < 1.5 := by
      apply (sq_lt_sq₀ (sqrt_nonneg _) (by norm_num)).mp
      rw [sq_sqrt (by norm_num)]
      norm_num
    linarith only [root]
  have above : π / 2 ≤ polarCornerAngle i := by
    by_contra! h
    have le := sin_le_sin_of_le_of_le_pi_div_two
      (show -(π / 2) ≤ polarCornerAngle i / 2 by linarith only [nonnegative, pi_pos])
      (show π / 4 ≤ π / 2 by linarith only [pi_pos])
      (show polarCornerAngle i / 2 ≤ π / 4 by linarith only [h])
    linarith only [le, below, polar_corner_halfSine_gt positive small i]
  rw [min_eq_right above, sin_pi_div_two]

/-- Both alternatives in the crossing estimate are at most 0.640 times the side count
of the actual polar polygon, using the actual longest side. -/
theorem polar_crossing_cutoff_le {a : ℝ} (positive : 0 < a) (small : a ≤ π / 6) :
    ∃ i : Fin (rowSize a 0), (∀ j : Fin (rowSize a 0), polarSideLength j ≤ polarSideLength i) ∧
      let l := polarSideLength i
      let c := 2 * l / (π * sin l)
      max (∑ j : Fin (rowSize a 0), c / sin (min (polarCornerAngle j) (π / 2)))
        (polarPerimeter a / (π * polarSideCutoff a)) ≤ 0.640 * (rowSize a 0 : ℝ) := by
  let k := rowSize a 0
  let R := tan (polarRadius a)
  have k_pos : 0 < k := rowSize_pos positive small (Nat.zero_le _)
  let : Nonempty (Fin k) := ⟨⟨0, k_pos⟩⟩
  obtain ⟨i, _, longest⟩ := Finset.exists_max_image Finset.univ
    (polarSideLength : Fin k → ℝ) Finset.univ_nonempty
  refine ⟨i, fun j => longest j (Finset.mem_univ j), max_le ?_ ?_⟩
  · have length := polarSideLength_pos positive small i
    have upper := polarSideLength_lt positive small i
    have sn := sin_pos_of_pos_of_lt_pi length (by linarith only [upper, pi_gt_d2])
    have lc : polarSideLength i ^ 3 ≤ 0.124 ^ 2 * polarSideLength i := by
      have sq := pow_le_pow_left₀ length.le upper.le 2
      nlinarith only [mul_le_mul_of_nonneg_right sq length.le]
    have factor : 2 * polarSideLength i / (π * sin (polarSideLength i)) ≤ 0.640 := by
      apply (div_le_iff₀ (mul_pos pi_pos sn)).mpr
      have h := mul_le_mul_of_nonneg_right (show (3.1415 : ℝ) ≤ π by linarith only [pi_gt_d4]) sn.le
      have sine := sin_gt_sub_cube length
      norm_num1 at lc h sine ⊢
      linarith only [h, sine, lc, length]
    calc
      _ ≤ ∑ _ : Fin k, (0.640 : ℝ) := Finset.sum_le_sum (fun j _ => by
        rw [polar_corner_capped_sine positive small j, div_one]
        exact factor)
      _ = _ := by simp; ring
  · have R_pos := (tan_polarRadius_bounds positive small).1
    have k_pos_real : 0 < (k : ℝ) := Nat.cast_pos.mpr k_pos
    have cutoff := (polarSideCutoff_bounds positive small).1
    apply (div_le_iff₀ (mul_pos pi_pos cutoff)).mpr
    have equal : 0.640 * (k : ℝ) * (π * polarSideCutoff a) = 2.560 * π * R := by
      change 0.640 * (k : ℝ) * (π * (4 * R / (k : ℝ))) = _
      field_simp [k_pos_real.ne']
      ring
    rw [equal]
    have h := polarPerimeter_le positive small
    nlinarith only [h, mul_pos pi_pos R_pos]

end Unfoldings.FewestNets.RevisedLatitudeGrid
