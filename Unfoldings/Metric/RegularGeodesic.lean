module

public import Unfoldings.Basic
public import Unfoldings.Metric.BallChart
public import Unfoldings.Path.ConvexChart
public import Mathlib.Analysis.InnerProductSpace.Convex

/-! A genuine Euclidean ball chart contains a nonconstant geodesic through its center. -/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings

variable {X : Type*} [EMetricSpace X] {x : X}

theorem HasMetricBallChart.exists_geodesic_through (regular : HasMetricBallChart Plane x) :
    ∃ a b : X, ∃ p : Path a b, p.IsGeodesic ∧ a ≠ b ∧
      ∃ t : unitInterval, t ∈ Set.Ioo (0 : unitInterval) 1 ∧ p t = x := by
  obtain ⟨r, positive, center, ⟨chart⟩⟩ := regular
  let origin : Metric.eball x (ENNReal.ofReal r) :=
    ⟨x, Metric.mem_eball_self (ENNReal.ofReal_pos.mpr positive)⟩
  let w : Plane := (chart origin).val
  obtain ⟨δ, δpos, ball⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball w (chart origin).property
  let v : Plane := (δ / 2) • EuclideanSpace.single 0 1
  have unit : ‖(EuclideanSpace.single 0 1 : Plane)‖ = 1 :=
    EuclideanSpace.orthonormal_single.norm_eq_one 0
  have vnorm : ‖v‖ = δ / 2 := by
    rw [norm_smul, unit, mul_one, Real.norm_of_nonneg (by positivity)]
  have vne : v ≠ 0 := norm_ne_zero_iff.mp (by rw [vnorm]; positivity)
  have left_mem : w - v ∈ Metric.ball center r := by
    apply ball
    rw [Metric.mem_ball, dist_eq_norm]
    have difference : (w - v) - w = -v := by abel
    rw [difference, norm_neg, vnorm]
    linarith
  have right_mem : w + v ∈ Metric.ball center r := by
    apply ball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, vnorm]
    linarith
  let left : Metric.ball center r := ⟨w - v, left_mem⟩
  let right : Metric.ball center r := ⟨w + v, right_mem⟩
  let q := (Path.segment left.val right.val).codRestrict (Metric.ball center r)
    left.property right.property
    (fun t => (convex_ball center r).lineMap_mem left.property right.property t.property)
  let f : Metric.ball center r → X := Subtype.val ∘ chart.symm
  have isometry : Isometry f :=
    (isometry_subtype_coe (s := Metric.eball x (ENNReal.ofReal r))).comp chart.symm.isometry
  let p := q.map isometry.continuous
  have segment_geodesic : (Path.segment left.val right.val).IsGeodesic :=
    (Path.segment left.val right.val).isGeodesic_of_lipschitz (Path.segment_lipschitz _ _)
  have restricted : q.IsGeodesic := segment_geodesic.codRestrict _ left.property right.property
    (fun t => (convex_ball center r).lineMap_mem left.property right.property t.property)
  have geodesic : p.IsGeodesic := restricted.map_isometry f isometry
  have distinct : f left ≠ f right := by
    intro equal
    have coordinates := congrArg Subtype.val (isometry.injective equal)
    change w - v = w + v at coordinates
    have self_neg : -v = v := add_left_cancel (by simpa only [sub_eq_add_neg] using coordinates)
    have two : (2 : ℝ) • v = 0 := by
      rw [two_smul]
      exact (congrArg (fun z : Plane => z + v) self_neg.symm).trans (neg_add_cancel v)
    exact vne ((smul_eq_zero.mp two).resolve_left two_ne_zero)
  let half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have middle : AffineMap.lineMap (w - v) (w + v) (half : ℝ) = w := by
    simpa only [midpoint, invOf_eq_inv, half, one_div] using midpoint_sub_add ℝ w v
  have at_half : p half = x := by
    have point : q half = chart origin := Subtype.ext middle
    change f (q half) = x
    rw [point]
    exact congrArg Subtype.val (chart.symm_apply_apply origin)
  have internal : half ∈ Set.Ioo (0 : unitInterval) 1 := by
    constructor
    · change (0 : ℝ) < 1 / 2
      norm_num
    · change (1 / 2 : ℝ) < 1
      norm_num
  exact ⟨f left, f right, p, geodesic, distinct, half, internal, at_half⟩

end Unfoldings
