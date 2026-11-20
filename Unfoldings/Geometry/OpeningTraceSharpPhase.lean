module

public import Unfoldings.Geometry.HingeCircleLiftBound
public import Unfoldings.Geometry.OpeningCircleTrace
public import Unfoldings.Geometry.OpeningPhaseSum
public import Unfoldings.Geometry.TwoBankAngle

/-! Sum the true fixed-radius opening increments along the actual bank trace. -/

@[expose] public section

noncomputable section

open scoped BigOperators NNReal

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n) (events : List (Opening n))
  (nonzero : R.direction ≠ 0) (states : ∀ k, (R.openingPrefix events k).Outward)

variable
  (sweeps : ∀ (k : Fin events.length) (θ : Set.Icc 0 (events.get k).angle),
    ((R.openingPrefix events k.val).rotateSuffix (events.get k).hinge θ.val).Outward)
  (suffixes : ∀ k : Fin events.length,
    ((R.openingPrefix events k.val).suffix (events.get k).hinge).Outward)
  (positive : ∀ k : Fin events.length, 0 < (events.get k).angle)
  (small : ∀ k : Fin events.length, (events.get k).angle < Real.pi)

include nonzero states sweeps suffixes positive small in
/-- If every active opening obeys a common circle-speed bound, the true relative phase
is positive whenever that bound times the total opening angle is below `π`. -/
theorem openingTrace_final_positive_phase_of_speed
    {L : ℝ} (speed_nonneg : 0 ≤ L) (budget : L * openingBudget events < Real.pi)
    (speed : ∀ (k : Fin events.length)
      (r : Set.Ioi (nndist (R.openingPrefix events k.val).start
        ((R.openingPrefix events k.val).chain.vertex (events.get k).hinge))),
      (R.openingPrefix events k.val).hingeCircleLift (events.get k).hinge
        (R.openingPrefix_direction_ne_zero events k.val nonzero) (events.get k).angle
        (fun θ hθ => sweeps k ⟨θ, hθ⟩) (positive k) r
        ⟨(events.get k).angle, (positive k).le, le_rfl⟩ ≤ L * (events.get k).angle)
    (first : Fin events.length) (source_hinge : (events.get first).hinge = 0)
    (r : ℝ≥0) (radius_positive : 0 < r) :
    0 < (R.twoBankRatio (R.openingPrefix events events.length) (states 0) nonzero
      (states events.length)
      (R.openingPrefix_direction_ne_zero events events.length nonzero) r).im := by
  let direction (i : Fin (events.length + 1)) : Circle :=
    (R.openingPrefix events i.val).circleDirection (states i.val)
      (R.openingPrefix_direction_ne_zero events i.val nonzero) r radius_positive
  let active (k : Fin events.length) : Prop :=
    nndist (R.openingPrefix events k.val).start
      ((R.openingPrefix events k.val).chain.vertex (events.get k).hinge) < r
  classical
  let turn (k : Fin events.length) : ℝ :=
    if h : active k then
      (R.openingPrefix events k.val).hingeCircleLift (events.get k).hinge
        (R.openingPrefix_direction_ne_zero events k.val nonzero) (events.get k).angle
        (fun θ hθ => sweeps k ⟨θ, hθ⟩) (positive k) ⟨r, h⟩
        ⟨(events.get k).angle, (positive k).le, le_rfl⟩
    else 0
  have active_pos (k : Fin events.length) (h : active k) : 0 < turn k := by
    rw [show turn k = _ from dite_eq_left h, (R.openingPrefix events k.val).hingeCircleLift_last]
    exact ((R.openingPrefix events k.val).hingeCircleAngle_bounds (events.get k).hinge
      (R.openingPrefix_direction_ne_zero events k.val nonzero) (events.get k).angle
      (fun θ hθ => sweeps k ⟨θ, hθ⟩) (suffixes k) (positive k) (small k)
      (⟨(events.get k).angle, positive k, le_rfl⟩, ⟨r, h⟩)).1
  have steps (k : Fin events.length) :
      Circle.exp (turn k) = direction k.succ / direction k.castSucc := by
    let Q := R.openingPrefix events k.val
    let move := Q.hingeSweepDirection (events.get k).hinge
      (R.openingPrefix_direction_ne_zero events k.val nonzero) (events.get k).angle
      (fun θ hθ => sweeps k ⟨θ, hθ⟩) r radius_positive
    let start : Set.Icc 0 (events.get k).angle := ⟨0, le_rfl, (positive k).le⟩
    let finish : Set.Icc 0 (events.get k).angle := ⟨(events.get k).angle, (positive k).le, le_rfl⟩
    have at_start : move start = direction k.castSucc := by
      unfold move hingeSweepDirection start
      change (Q.rotateSuffix (events.get k).hinge 0).circleDirection _ _ r radius_positive =
        Q.circleDirection _ _ r radius_positive
      congr 1
      exact Q.rotateSuffix_zero _
    have at_finish : move finish = direction k.succ := by
      unfold move hingeSweepDirection finish
      change (Q.rotateSuffix (events.get k).hinge (events.get k).angle).circleDirection
          _ _ r radius_positive =
        (R.openingPrefix events (k.val + 1)).circleDirection _ _ r radius_positive
      congr 1
      exact (R.openingPrefix_succ events k).symm
    rw [← at_start, ← at_finish]
    by_cases h : active k
    · rw [show turn k = _ from dite_eq_left h, Q.exp_hingeCircleLift]
      have exterior (θ : Set.Icc 0 (events.get k).angle) :=
        Q.hingeSweepDirection_eq_exterior (events.get k).hinge
          (R.openingPrefix_direction_ne_zero events k.val nonzero) (events.get k).angle
          (fun t ht => sweeps k ⟨t, ht⟩) ⟨r, h⟩ radius_positive θ
      rw [← exterior start, ← exterior finish]
    · have below : (r : ℝ) ≤ dist Q.start (Q.chain.vertex (events.get k).hinge) :=
        NNReal.coe_le_coe.mpr (le_of_not_gt h)
      have unchanged (θ : Set.Icc 0 (events.get k).angle) :
          move θ = Q.circleDirection (states k.val)
            (R.openingPrefix_direction_ne_zero events k.val nonzero) r radius_positive :=
        Q.hingeSweepDirection_eq_of_below _ _ _ _ (states k.val) _ _ below θ
      rw [show turn k = 0 from dite_eq_right h, Circle.exp_zero, unchanged start, unchanged finish,
        div_self']
  have nonnegative (k : Fin events.length) : 0 ≤ turn k := by
    by_cases h : active k
    · exact (active_pos k h).le
    · rw [show turn k = 0 from dite_eq_right h]
  have strict : ∃ k, 0 < turn k := by
    refine ⟨first, active_pos first ?_⟩
    change nndist (R.openingPrefix events first.val).start
      ((R.openingPrefix events first.val).chain.vertex (events.get first).hinge) < r
    rw [source_hinge]
    simpa only [PolygonalRay.start, nndist_self] using radius_positive
  have bound (k : Fin events.length) : turn k ≤ L * (events.get k).angle := by
    by_cases h : active k
    · exact (show turn k = _ from dite_eq_left h).trans_le (speed k ⟨r, h⟩)
    · rw [show turn k = 0 from dite_eq_right h]
      exact mul_nonneg speed_nonneg (positive k).le
  have sum_budget : (∑ k : Fin events.length, (events.get k).angle) = openingBudget events := by
    rw [← List.sum_ofFn, openingBudget,
      ← List.ofFn_getElem_eq_map events (fun event => |event.angle|)]
    congr 2
    funext k
    exact (abs_of_pos (positive k)).symm
  have sum_small : (∑ k, turn k) < Real.pi := by
    apply (Finset.sum_le_sum (fun k _ => bound k)).trans_lt
    rw [← Finset.mul_sum, sum_budget]
    exact budget
  have phase := circle_final_ratio_im_pos_of_sum direction turn steps nonnegative strict sum_small
  rw [Circle.coe_div] at phase
  exact phase

end Unfoldings.PolygonalRay
