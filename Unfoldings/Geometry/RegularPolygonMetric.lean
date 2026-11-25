module

public import Unfoldings.Geometry.RegularPolygonFan
public import Unfoldings.Geometry.HeadingChordError

/-! Distances between sides and corners of an actual regular planar selector. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real InnerProductGeometry

private theorem polarRay_inner_metric (x y : ℝ) :
    inner ℝ (polarRay x) (polarRay y) = cos (y - x) := by
  rw [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, polarRay_re, polarRay_im,
    polarRay_re, polarRay_im, cos_sub]
  ring

private theorem sin_le_sin_of_between {x y : ℝ} (nonnegative : 0 ≤ x)
    (left : x ≤ y) (right : y ≤ π - x) : sin x ≤ sin y := by
  by_cases before : y ≤ π / 2
  · exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) before left
  · rw [← sin_pi_sub y]
    exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) (by linarith only [before])
      (by linarith only [right])

variable (frame : Plane ≃ₗᵢ[ℝ] ℂ)

set_option maxHeartbeats 1000000 in
-- The two convex segment bounds share the same rotating linear functional.
/-- Ordered nonincident sides are separated by a line through the center
bisecting their midpoint headings. The separation controls every pair of points. -/
theorem regularRingSide_dist_ge {k i j : ℕ} (enough : 6 ≤ k)
    (before : i + 2 ≤ j) (after : j + 2 ≤ i + k) {R : ℝ} (radius : 0 ≤ R)
    {p q : Plane} (hp : p ∈ segment ℝ (regularRingVertex frame k R i)
      (regularRingVertex frame k R (i + 1)))
    (hq : q ∈ segment ℝ (regularRingVertex frame k R j) (regularRingVertex frame k R (j + 1))) :
    2 * R * sin (π / k) ≤ dist p q := by
  let h := π / (k : ℝ)
  let μ := ((i : ℝ) + j + 1) * h
  let phase (m : ℕ) := 2 * (m : ℝ) * h
  let axis := frame.symm (polarRay (μ + π / 2))
  have k_pos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have h_pos : 0 < h := div_pos pi_pos k_pos
  have period : (k : ℝ) * h = π := by dsimp only [h]; field_simp
  have low : (i : ℝ) + 2 ≤ j := by exact_mod_cast before
  have high : (j : ℝ) + 2 ≤ (i : ℝ) + k := by exact_mod_cast after
  have gap_small : h ≤ ((j : ℝ) - i - 1) * h ∧ ((j : ℝ) - i - 1) * h ≤ π - h := by
    constructor
    · have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (j : ℝ) - i - 1 by linarith only [low]) h_pos.le
      linarith
    · have := mul_le_mul_of_nonneg_right
        (show (j : ℝ) - i - 1 ≤ (k : ℝ) - 1 by linarith only [high]) h_pos.le
      linarith only [this, period]
  have gap_large : h ≤ ((j : ℝ) - i + 1) * h ∧ ((j : ℝ) - i + 1) * h ≤ π - h := by
    constructor
    · have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (j : ℝ) - i + 1 by linarith only [low]) h_pos.le
      linarith
    · have := mul_le_mul_of_nonneg_right
        (show (j : ℝ) - i + 1 ≤ (k : ℝ) - 1 by linarith only [high]) h_pos.le
      linarith only [this, period]
  have dot (m : ℕ) : inner ℝ axis (regularRingVertex frame k R m) =
      R * sin (phase m - μ) := by
    rw [regularRingVertex, inner_smul_right]
    change R * inner ℝ (frame.symm (polarRay (μ + π / 2))) (frame.symm (polarRay (phase m))) = _
    rw [frame.symm.inner_map_map, polarRay_inner_metric,
      show phase m - (μ + π / 2) = phase m - μ - π / 2 by ring, cos_sub,
      cos_pi_div_two, sin_pi_div_two, mul_zero, zero_add, mul_one]
  have i_left : phase i - μ = -(((j : ℝ) - i + 1) * h) := by dsimp only [phase, μ]; ring
  have i_right : phase (i + 1) - μ = -(((j : ℝ) - i - 1) * h) := by
    dsimp only [phase, μ]
    push_cast
    ring
  have j_left : phase j - μ = ((j : ℝ) - i - 1) * h := by dsimp only [phase, μ]; ring
  have j_right : phase (j + 1) - μ = ((j : ℝ) - i + 1) * h := by
    dsimp only [phase, μ]
    push_cast
    ring
  have h_small := sin_le_sin_of_between h_pos.le gap_small.1 gap_small.2
  have h_large := sin_le_sin_of_between h_pos.le gap_large.1 gap_large.2
  let f : Plane →ₗ[ℝ] ℝ := (innerSL ℝ axis).toLinearMap
  have left_convex : Convex ℝ {z : Plane | inner ℝ axis z ≤ -(R * sin h)} :=
    (convex_Iic _).linear_preimage f
  have right_convex : Convex ℝ {z : Plane | R * sin h ≤ inner ℝ axis z} :=
    (convex_Ici _).linear_preimage f
  have left_bound : inner ℝ axis p ≤ -(R * sin h) :=
    left_convex.segment_subset
      (show inner ℝ axis (regularRingVertex frame k R i) ≤ -(R * sin h) by
        rw [dot, i_left, sin_neg, mul_neg]
        exact neg_le_neg (mul_le_mul_of_nonneg_left h_large radius))
      (show inner ℝ axis (regularRingVertex frame k R (i + 1)) ≤ -(R * sin h) by
        rw [dot, i_right, sin_neg, mul_neg]
        exact neg_le_neg (mul_le_mul_of_nonneg_left h_small radius)) hp
  have right_bound : R * sin h ≤ inner ℝ axis q :=
    right_convex.segment_subset
      (show R * sin h ≤ inner ℝ axis (regularRingVertex frame k R j) by
        rw [dot, j_left]
        exact mul_le_mul_of_nonneg_left h_small radius)
      (show R * sin h ≤ inner ℝ axis (regularRingVertex frame k R (j + 1)) by
        rw [dot, j_right]
        exact mul_le_mul_of_nonneg_left h_large radius) hq
  have axis_unit : ‖axis‖ = 1 := (frame.symm.norm_map _).trans (norm_polarRay _)
  have distance := abs_real_inner_le_norm axis (q - p)
  rw [axis_unit, one_mul, inner_sub_right, ← dist_eq_norm, dist_comm q p] at distance
  exact (show 2 * R * sin h ≤ inner ℝ axis q - inner ℝ axis p by
    linarith only [left_bound, right_bound]).trans ((le_abs_self _).trans distance)

private theorem polarRay_dist_eq (t u : ℝ) :
    dist (polarRay t) (polarRay u) = 2 * |sin ((u - t) / 2)| := by
  rw [dist_eq_norm]
  have squared := norm_sub_pow_two_real (polarRay t) (polarRay u)
  rw [norm_polarRay, norm_polarRay, polarRay_inner_metric,
    show u - t = 2 * ((u - t) / 2) by ring, cos_two_mul] at squared
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, sq_abs]
  nlinarith only [squared, sin_sq_add_cos_sq ((u - t) / 2)]

/-- The exact length of any planar chord in the selector ring. -/
theorem regularRingVertex_dist_eq (k i j : ℕ) {R : ℝ} (radius : 0 ≤ R) :
    dist (regularRingVertex frame k R i) (regularRingVertex frame k R j) =
      2 * R * |sin (((j : ℝ) - i) * (π / k))| := by
  simp only [regularRingVertex, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg radius, ← map_sub, frame.symm.norm_map]
  rw [← dist_eq_norm, polarRay_dist_eq, show (2 * (j : ℝ) * (π / k) - 2 * (i : ℝ) * (π / k)) / 2 =
    ((j : ℝ) - i) * (π / k) by ring]
  ring

/-- Every side has the exact common chord length of the regular planar polygon. -/
theorem regularRingVertex_dist_succ {k : ℕ} (enough : 6 ≤ k) (i : ℕ) {R : ℝ} (radius : 0 ≤ R) :
    dist (regularRingVertex frame k R i) (regularRingVertex frame k R (i + 1)) =
      2 * R * sin (π / k) := by
  have k_pos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have step_pos : 0 < π / (k : ℝ) := div_pos pi_pos k_pos
  have step_le : π / (k : ℝ) ≤ π / 6 :=
    div_le_div_of_nonneg_left pi_pos.le (by norm_num) (by exact_mod_cast enough)
  rw [regularRingVertex_dist_eq frame k i (i + 1) radius,
    show ((i + 1 : ℕ) : ℝ) - i = 1 by push_cast; ring, one_mul,
    abs_of_pos (sin_pos_of_pos_of_lt_pi step_pos (by linarith only [step_le, pi_pos]))]

private theorem norm_unit_sub_eq_sin_half {u v : Plane} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - v‖ = 2 * sin (angle u v / 2) := by
  have squared := norm_sub_pow_two_real u v
  rw [hu, hv, inner_eq_cos_angle_of_norm_eq_one hu hv,
    show angle u v = 2 * (angle u v / 2) by ring, cos_two_mul] at squared
  have sine : 0 ≤ sin (angle u v / 2) := sin_nonneg_of_nonneg_of_le_pi
    (div_nonneg (angle_nonneg u v) zero_le_two) (by linarith only [angle_le_pi u v, pi_pos])
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    (by nlinarith only [squared, sin_sq_add_cos_sq (angle u v / 2)])

/-- The base half-angle sine of the actual regular polygon corner is its
apothem divided by its circumradius. Indices may wrap around the full ring. -/
theorem regularRingCorner_half_sine {k : ℕ} (enough : 6 ≤ k) (i : ℕ) {R : ℝ}
    (radius : 0 < R) :
    let P := regularRingVertex frame k R
    sin (angle (P i - P (i + 1)) (P (i + 2) - P (i + 1)) / 2) = cos (π / k) := by
  let P := regularRingVertex frame k R
  let h := π / (k : ℝ)
  let L := 2 * R * sin h
  have k_pos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have h_pos : 0 < h := div_pos pi_pos k_pos
  have h_le : h ≤ π / 6 := div_le_div_of_nonneg_left pi_pos.le (by norm_num)
    (by exact_mod_cast enough)
  have sine := sin_pos_of_pos_of_lt_pi h_pos (by linarith only [h_le, pi_pos])
  have sine_double : 0 < sin (2 * h) := sin_pos_of_pos_of_lt_pi (by positivity)
    (by linarith only [h_le, pi_pos])
  have positive : 0 < L := by unfold L; positivity
  have first : ‖P i - P (i + 1)‖ = L :=
    (dist_eq_norm _ _).symm.trans (regularRingVertex_dist_succ frame enough i radius.le)
  have last : ‖P (i + 2) - P (i + 1)‖ = L :=
    (dist_eq_norm _ _).symm.trans ((dist_comm _ _).trans
      (regularRingVertex_dist_succ frame enough (i + 1) radius.le))
  have diagonal : ‖P i - P (i + 2)‖ = 2 * R * sin (2 * h) := by
    rw [← dist_eq_norm, regularRingVertex_dist_eq frame k i (i + 2) radius.le,
      show ((i + 2 : ℕ) : ℝ) - i = 2 by push_cast; ring, abs_of_pos sine_double]
  let u := L⁻¹ • (P i - P (i + 1))
  let v := L⁻¹ • (P (i + 2) - P (i + 1))
  have unit (z : Plane) (equal : ‖z‖ = L) : ‖L⁻¹ • z‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr positive), equal, inv_mul_cancel₀ positive.ne']
  have chord := norm_unit_sub_eq_sin_half (unit _ first) (unit _ last)
  change ‖u - v‖ = 2 * sin (angle u v / 2) at chord
  have norm_eq : ‖u - v‖ = 2 * cos h := by
    dsimp only [u, v]
    rw [← smul_sub, show (P i - P (i + 1)) - (P (i + 2) - P (i + 1)) = P i - P (i + 2) by abel,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr positive), diagonal]
    change (2 * R * sin h)⁻¹ * (2 * R * sin (2 * h)) = _
    rw [sin_two_mul]
    field_simp [radius.ne', sine.ne']
  change sin (angle (P i - P (i + 1)) (P (i + 2) - P (i + 1)) / 2) = cos h
  have angles : angle u v = angle (P i - P (i + 1)) (P (i + 2) - P (i + 1)) := by
    dsimp only [u, v]
    rw [angle_smul_left_of_pos _ _ (inv_pos.mpr positive),
      angle_smul_right_of_pos _ _ (inv_pos.mpr positive)]
  rw [norm_eq, angles] at chord
  linarith only [chord]

end Unfoldings
