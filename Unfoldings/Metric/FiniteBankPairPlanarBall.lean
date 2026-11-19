module

public import Unfoldings.Metric.BankPairPlanarBall

/-! Affine bank parameters match two charts and fill the common diameter. -/

@[expose] public section

open scoped ENNReal

namespace Unfoldings.MetricGluing

section Affine

variable {I A : Type*} (X : I → Type*) [∀ i, EMetricSpace (X i)] {i j : I}
  (left : A → X i) (right : A → X j) (t : A)

local notation "Glue" => bankPairGlue X left right
local notation "Center" => fun side : Bool =>
  Bool.rec (Sigma.mk i (left t)) (Sigma.mk j (right t)) side

variable (param : A → ℝ)

/-- At an interior parameter, common signed arclength matches both chart sides and covers
the entire short diameter. -/
theorem bankPair_planarBall_of_affine_coordinates {R speed : ℝ} (C : BankPairChart X Center R)
    (speed_pos : 0 < speed) (interior_time : param t ∈ interior (Set.range param))
    (left_metric : ∀ s, edist (left t) (left s) = ENNReal.ofReal (|param s - param t| * speed))
    (right_metric : ∀ s, edist (right t) (right s) =
      ENNReal.ofReal (|param s - param t| * speed))
    (clear_left : ∀ s, ENNReal.ofReal R ≤ faceCost X ⟨j, right t⟩ ⟨i, left s⟩)
    (clear_right : ∀ s, ENNReal.ofReal R ≤ faceCost X ⟨i, left t⟩ ⟨j, right s⟩)
    (left_coord : ∀ s (_near : C.Near false ⟨i, left s⟩),
      C.coordinates ⟨i, left s⟩ = (((param s - param t) * speed : ℝ) : ℂ))
    (right_coord : ∀ s (_near : C.Near true ⟨j, right s⟩),
      C.coordinates ⟨j, right s⟩ = (((param s - param t) * speed : ℝ) : ℂ)) :
    HasMetricBallChart ℂ (point X Glue ⟨i, left t⟩) := by
  obtain ⟨ε, εpos, interval⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp interior_time)
  let r := min (R / 4) (ε * speed)
  have rpos : 0 < r := lt_min (div_pos C.positive (by norm_num)) (mul_pos εpos speed_pos)
  have small : 4 * r ≤ R := by
    have le : r ≤ R / 4 := min_le_left _ _
    linarith
  have included : r ≤ R := by linarith
  have same (s : A) : edist (left t) (left s) = edist (right t) (right s) :=
    (left_metric s).trans (right_metric s).symm
  have matched (s : A) (near : C.Near false ⟨i, left s⟩) :
      C.coordinates ⟨i, left s⟩ = C.coordinates ⟨j, right s⟩ := by
    have other : C.Near true ⟨j, right s⟩ := by
      change faceCost X ⟨j, right t⟩ ⟨j, right s⟩ < ENNReal.ofReal R
      change faceCost X ⟨i, left t⟩ ⟨i, left s⟩ < ENNReal.ofReal R at near
      rwa [faceCost_same_tag, ← same, ← faceCost_same_tag]
    exact (left_coord s near).trans (right_coord s other).symm
  apply bankPair_planarBall X left right t C rpos small same clear_left clear_right matched
  intro z axis
  have radius : ‖z.val‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using z.property
  have real_radius : |z.val.re| < r := (Complex.abs_re_le_norm _).trans_lt radius
  have small_real : |z.val.re| < ε * speed := real_radius.trans_le (min_le_right _ _)
  have time_near : param t + z.val.re / speed ∈ Metric.ball (param t) ε := by
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_div, abs_of_pos speed_pos,
      div_lt_iff₀ speed_pos]
    exact small_real
  obtain ⟨s, time⟩ := interval time_near
  have displacement : (param s - param t) * speed = z.val.re := by
    rw [time, add_sub_cancel_left, div_mul_cancel₀ _ speed_pos.ne']
  have named : (((param s - param t) * speed : ℝ) : ℂ) = z.val := by
    rw [displacement]
    exact Complex.ext (by simp) (by simpa only [Complex.ofReal_im] using axis.symm)
  have radial : ENNReal.ofReal (|param s - param t| * speed) < ENNReal.ofReal R := by
    rw [← abs_of_pos speed_pos, ← abs_mul, displacement]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg _)
      |>.mpr (real_radius.trans_le included)
  have lnear : C.Near false ⟨i, left s⟩ := by
    change faceCost X ⟨i, left t⟩ ⟨i, left s⟩ < ENNReal.ofReal R
    rw [faceCost_same_tag, left_metric]
    exact radial
  have rnear : C.Near true ⟨j, right s⟩ := by
    change faceCost X ⟨j, right t⟩ ⟨j, right s⟩ < ENNReal.ofReal R
    rw [faceCost_same_tag, right_metric]
    exact radial
  have patch_eq (side : Bool) (b : Total X) (near : C.Near side b)
      (coord : C.coordinates b = z.val) (w : bankHalfDisk side r) (value : w.val = z.val) :
      C.patch included side w = b := by
    unfold BankPairChart.patch
    have named := (C.coordinates_near side b near).symm.trans (coord.trans value.symm)
    have chart_eq : C.chart side (C.nearPoint side b near) =
        ⟨w.val, Metric.ball_subset_ball included w.property.1, w.property.2⟩ :=
      Subtype.ext named
    rw [← chart_eq, (C.chart side).symm_apply_apply, C.tagged_nearPoint]
  rw [patch_eq false _ lnear ((left_coord s lnear).trans named) _ rfl,
    patch_eq true _ rnear ((right_coord s rnear).trans named) _ rfl]
  exact point_eq_of_glue X ⟨s, rfl, rfl⟩


end Affine

section Finite

variable {I : Type*} (X : I → Type*) [∀ i, EMetricSpace (X i)] {i j : I}
  (left : unitInterval → X i) (right : unitInterval → X j) (t : unitInterval)

local notation "Glue" => bankPairGlue X left right
local notation "Center" => fun side : Bool =>
  Bool.rec (Sigma.mk i (left t)) (Sigma.mk j (right t)) side

/-- Near a strict finite parameter, common signed arclength matches both chart sides
and covers the entire short diameter. -/
theorem finiteBankPair_planarBall {R speed : ℝ} (C : BankPairChart X Center R)
    (speed_pos : 0 < speed) (bounds : 0 < t ∧ t < 1)
    (left_metric : ∀ s, edist (left t) (left s) = ENNReal.ofReal (|(s : ℝ) - t| * speed))
    (right_metric : ∀ s, edist (right t) (right s) =
      ENNReal.ofReal (|(s : ℝ) - t| * speed))
    (clear_left : ∀ s, ENNReal.ofReal R ≤ faceCost X ⟨j, right t⟩ ⟨i, left s⟩)
    (clear_right : ∀ s, ENNReal.ofReal R ≤ faceCost X ⟨i, left t⟩ ⟨j, right s⟩)
    (left_coord : ∀ s (_near : C.Near false ⟨i, left s⟩),
      C.coordinates ⟨i, left s⟩ = ((((s : ℝ) - t) * speed : ℝ) : ℂ))
    (right_coord : ∀ s (_near : C.Near true ⟨j, right s⟩),
      C.coordinates ⟨j, right s⟩ = ((((s : ℝ) - t) * speed : ℝ) : ℂ)) :
    HasMetricBallChart ℂ (point X Glue ⟨i, left t⟩) := by
  apply bankPair_planarBall_of_affine_coordinates X left right t Subtype.val C speed_pos
    _ left_metric right_metric clear_left clear_right left_coord right_coord
  rw [Subtype.range_coe]
  change t.val ∈ interior (Set.Icc (0 : ℝ) 1)
  rw [interior_Icc]
  exact bounds

end Finite

end Unfoldings.MetricGluing
