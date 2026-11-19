module

public import Unfoldings.Metric.BankPairPlanarBall

/-! Affine original finite-bank parameters match the two charts and fill the common diameter. -/

@[expose] public section

open scoped ENNReal

namespace Unfoldings.MetricGluing

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
  let r := min (R / 4) (min (t.val * speed) ((1 - t.val) * speed))
  have rpos : 0 < r :=
    lt_min (div_pos C.positive (by norm_num))
      (lt_min (mul_pos bounds.1 speed_pos) (mul_pos (sub_pos.mpr bounds.2) speed_pos))
  have small : 4 * r ≤ R := by
    have le : r ≤ R / 4 := min_le_left _ _
    linarith
  have included : r ≤ R := by linarith
  have same (s : unitInterval) : edist (left t) (left s) = edist (right t) (right s) :=
    (left_metric s).trans (right_metric s).symm
  have matched (s : unitInterval) (near : C.Near false ⟨i, left s⟩) :
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
  have first : r ≤ t.val * speed := (min_le_right _ _).trans (min_le_left _ _)
  have last : r ≤ (1 - t.val) * speed := (min_le_right _ _).trans (min_le_right _ _)
  have after : -t.val ≤ z.val.re / speed :=
    (le_div_iff₀ speed_pos).mpr (by linarith [(abs_lt.mp real_radius).1])
  have before : z.val.re / speed ≤ 1 - t.val :=
    (div_le_iff₀ speed_pos).mpr (by linarith [(abs_lt.mp real_radius).2])
  let s : unitInterval := ⟨t.val + z.val.re / speed, by linarith, by linarith⟩
  have displacement : (s.val - t.val) * speed = z.val.re := by
    dsimp [s]
    rw [add_sub_cancel_left, div_mul_cancel₀ _ speed_pos.ne']
  have named : (((s.val - t.val) * speed : ℝ) : ℂ) = z.val := by
    rw [displacement]
    exact Complex.ext (by simp) (by simpa only [Complex.ofReal_im] using axis.symm)
  have radial : ENNReal.ofReal (|s.val - t.val| * speed) < ENNReal.ofReal R := by
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

end Unfoldings.MetricGluing
