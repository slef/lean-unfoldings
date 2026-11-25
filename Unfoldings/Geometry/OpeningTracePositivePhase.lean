module

public import Unfoldings.Geometry.OpeningCircleTrace
public import Unfoldings.Geometry.TwoBankAngle

/-! A positive source opening makes the final actual bank strictly above the original bank. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n) (events : List (Opening n))
  (outward : R.Outward) (nonzero : R.direction ≠ 0)
  (states : ∀ k, (R.openingPrefix events k).Outward)

@[simp] theorem prefixCircleHeading_zero (r : ℝ≥0) (radius_positive : 0 < r) :
    R.prefixCircleHeading events outward nonzero states r radius_positive 0 = 0 := by
  simp only [prefixCircleHeading, openingPrefix, List.take_zero, openings, List.foldl_nil,
    div_self', Circle.coe_one, Complex.arg_one]

theorem prefixCircleHeading_eq_ratio_arg (r : ℝ≥0) (radius_positive : 0 < r) (k : ℕ) :
    R.prefixCircleHeading events outward nonzero states r radius_positive k =
      Complex.arg (R.twoBankRatio (R.openingPrefix events k) outward nonzero (states k)
        (R.openingPrefix_direction_ne_zero events k nonzero) r) := by
  unfold prefixCircleHeading
  rw [Circle.coe_div]
  rfl

variable (γ : ℝ≥0) (positive : 0 < γ) (small : γ ≤ 1)
  (budget : 3 * openingBudget events < (γ : ℝ) ^ 2)
  (margin : ∀ i, (γ : ℝ) * (‖R.chain.vertex i.castSucc - R.start‖ * ‖R.chain.edge i‖) ≤
    inner ℝ (R.chain.vertex i.castSucc - R.start) (R.chain.edge i))
  (tail_margin : (γ : ℝ) * (‖R.chain.vertex (Fin.last n) - R.start‖ * ‖R.direction‖) ≤
    inner ℝ (R.chain.vertex (Fin.last n) - R.start) R.direction)
  (sweeps : ∀ (k : Fin events.length) (θ : Set.Icc 0 (events[k.val]'k.isLt).angle),
    ((R.openingPrefix events k.val).rotateSuffix (events[k.val]'k.isLt).hinge θ.val).Outward)
  (suffixes : ∀ k : Fin events.length,
    ((R.openingPrefix events k.val).suffix (events[k.val]'k.isLt).hinge).Outward)
  (angles_positive : ∀ k : Fin events.length, 0 < (events[k.val]'k.isLt).angle)
  (angles_small : ∀ k : Fin events.length, (events[k.val]'k.isLt).angle < Real.pi)

include outward nonzero states sweeps suffixes angles_positive angles_small in
/-- A positive source opening gives positive final relative phase when
all later rotations remain in the common halfplane. -/
theorem prefixCircleHeading_final_pos_of_halfplane (first : Fin events.length)
    (at_start : first.val = 0) (source_hinge : (events[first.val]'first.isLt).hinge = 0)
    (r : ℝ≥0) (radius_positive : 0 < r)
    (halfplane : ∀ (k : Fin events.length) (θ : Set.Icc 0 events[k].angle),
      0 < ((((R.openingPrefix events k.val).hingeSweepDirection events[k].hinge
        (R.openingPrefix_direction_ne_zero events k.val nonzero) events[k].angle
        (fun ψ bounds => sweeps k ⟨ψ, bounds⟩) r radius_positive θ /
          R.circleDirection outward nonzero r radius_positive : Circle) : ℂ)).re) :
    0 < R.prefixCircleHeading events outward nonzero states r radius_positive events.length := by
  have above : dist (R.openingPrefix events first.val).start
      ((R.openingPrefix events first.val).chain.vertex
        (events[first.val]'first.isLt).hinge) < (r : ℝ) := by
    rw [source_hinge]
    change dist (R.openingPrefix events first.val).start
      (R.openingPrefix events first.val).start < (r : ℝ)
    simpa only [dist_self] using (show (0 : ℝ) < r from radius_positive)
  have strict := (R.openingPrefix events first.val).strictMono_hingeCommonHeading_of_above
    (events[first.val]'first.isLt).hinge
    (R.openingPrefix_direction_ne_zero events first.val nonzero)
    (events[first.val]'first.isLt).angle
    (fun ψ bounds => sweeps first ⟨ψ, bounds⟩) r radius_positive
    (R.circleDirection outward nonzero r radius_positive) (suffixes first)
    (angles_positive first) (angles_small first)
    (halfplane first) above
  have strict_step := strict (show
    (⟨0, le_rfl, (angles_positive first).le⟩ : Set.Icc 0 (events[first.val]'first.isLt).angle) <
      ⟨(events[first.val]'first.isLt).angle, (angles_positive first).le, le_rfl⟩ from
      angles_positive first)
  have next : R.openingPrefix events (first.val + 1) =
      (R.openingPrefix events first.val).rotateSuffix
        (events[first.val]'first.isLt).hinge (events[first.val]'first.isLt).angle :=
    R.openingPrefix_succ events first
  have first_step :
      R.prefixCircleHeading events outward nonzero states r radius_positive first.val <
      R.prefixCircleHeading events outward nonzero states r radius_positive (first.val + 1) := by
    simpa only [hingeCommonHeading, hingeSweepDirection, rotateSuffix_zero,
      prefixCircleHeading, Circle.coe_div, ← next] using strict_step
  rw [at_start, R.prefixCircleHeading_zero] at first_step
  have monotone : Monotone (fun k : Fin (events.length + 1) =>
      R.prefixCircleHeading events outward nonzero states r radius_positive k.val) := by
    apply Fin.monotone_iff_le_succ.mpr
    exact R.prefixCircleHeading_step_of_halfplane events outward nonzero states sweeps suffixes
      angles_positive angles_small r radius_positive halfplane
  have later := monotone (Fin.le_last first.succ)
  change R.prefixCircleHeading events outward nonzero states r radius_positive (first.val + 1) ≤
    R.prefixCircleHeading events outward nonzero states r radius_positive events.length at later
  rw [at_start] at later
  exact first_step.trans_le later

include outward nonzero states positive small budget margin tail_margin sweeps suffixes
  angles_positive angles_small in
/-- The initial positive opening at the actual source makes every later circle heading positive. -/
theorem prefixCircleHeading_final_pos (first : Fin events.length) (at_start : first.val = 0)
    (source_hinge : (events[first.val]'first.isLt).hinge = 0) (r : ℝ≥0) (radius_positive : 0 < r) :
    0 < R.prefixCircleHeading events outward nonzero states r radius_positive events.length := by
  exact R.prefixCircleHeading_final_pos_of_halfplane events outward nonzero states sweeps suffixes
    angles_positive angles_small first at_start source_hinge r radius_positive
    (fun j => R.openingPrefix_sweep_halfplane events outward nonzero γ positive small budget
      margin tail_margin sweeps j r radius_positive)

include outward nonzero states positive small budget margin tail_margin sweeps suffixes
  angles_positive angles_small in
/-- The actual final relative bank phase lies strictly in the upper semicircle at every radius. -/
theorem openingTrace_final_positive_phase (first : Fin events.length) (at_start : first.val = 0)
    (source_hinge : (events[first.val]'first.isLt).hinge = 0) (r : ℝ≥0) (radius_positive : 0 < r) :
    0 < (R.twoBankRatio (R.openingPrefix events events.length) outward nonzero
      (states events.length)
      (R.openingPrefix_direction_ne_zero events events.length nonzero) r).im := by
  have argument_positive := R.prefixCircleHeading_final_pos events outward nonzero states γ
    positive small budget margin tail_margin sweeps suffixes angles_positive angles_small
    first at_start source_hinge r radius_positive
  rw [R.prefixCircleHeading_eq_ratio_arg] at argument_positive
  have take_budget : 3 * openingBudget (events.take events.length) < (γ : ℝ) ^ 2 := by
    simpa only [List.take_length] using budget
  have halfplane := R.openings_circleDirection_halfplane outward nonzero
    (events.take events.length) (states events.length) γ positive small take_budget
    margin tail_margin r radius_positive
  rw [Circle.coe_div] at halfplane
  change 0 < (R.twoBankRatio (R.openingPrefix events events.length) outward nonzero
    (states events.length) (R.openingPrefix_direction_ne_zero events events.length nonzero) r).re
      at halfplane
  have argument_small := Complex.arg_lt_pi_iff.mpr (Or.inl halfplane.le)
  have sine := Real.sin_pos_of_pos_of_lt_pi argument_positive argument_small
  have identity := Complex.norm_mul_sin_arg
    (R.twoBankRatio (R.openingPrefix events events.length) outward nonzero
      (states events.length) (R.openingPrefix_direction_ne_zero events events.length nonzero) r)
  rw [R.norm_twoBankRatio _ outward nonzero (states events.length)
    (R.openingPrefix_direction_ne_zero events events.length nonzero) r radius_positive, one_mul]
      at identity
  exact identity ▸ sine

end Unfoldings.PolygonalRay
