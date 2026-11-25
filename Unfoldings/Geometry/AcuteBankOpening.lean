module

public import Unfoldings.Geometry.AcuteBankCone
public import Unfoldings.Geometry.OpeningTracePositivePhase
public import Unfoldings.Geometry.OrientedBankGap

/-! Positive suffix rotations in one common acute cone open a genuine bank gap. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalRay

open PolygonalChain
open scoped NNReal

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- Every intermediate bank stays outward and in a common angular halfplane.
The first positive rotation at the source makes the final bank strictly separate
from the original one at every positive radius. -/
theorem orientedGap_openings_of_acuteCone (events : List (Opening n))
    (nonzero : R.direction ≠ 0) {center : ℝ}
    (prefix_cone : ∀ k, (R.openingPrefix events k).InAcuteCone center)
    (during : ∀ (k : Fin events.length) (θ : Set.Icc 0 events[k.val].angle),
      ((R.openingPrefix events k.val).rotateSuffix events[k.val].hinge θ.val).InAcuteCone center)
    (angles_positive : ∀ k : Fin events.length, 0 < events[k.val].angle)
    (angles_small : ∀ k : Fin events.length, events[k.val].angle < Real.pi)
    (first : Fin events.length) (at_start : first.val = 0)
    (source_hinge : (events[first.val]'first.isLt).hinge = 0) :
    OrientedBankGap R (R.openings events) := by
  have start : R.InAcuteCone center := by
    simpa only [openingPrefix, List.take_zero, openings, List.foldl_nil] using prefix_cone 0
  let outward := start.outward R
  let states (k : ℕ) := (prefix_cone k).outward (R.openingPrefix events k)
  have suffix (k : Fin events.length) :
      ((R.openingPrefix events k.val).suffix events[k.val].hinge).Outward :=
    ((prefix_cone k.val).suffix _ _).outward _
  let sweeps (k : Fin events.length) (θ : Set.Icc 0 events[k.val].angle) :=
    (during k θ).outward _
  let Q := R.openingPrefix events events.length
  have direction_ne_zero := R.openingPrefix_direction_ne_zero events events.length nonzero
  have phase (r : ℝ≥0) (hr : 0 < r) :
      0 < (R.twoBankRatio Q outward nonzero (states events.length) direction_ne_zero r).im := by
    have halfplane (k : Fin events.length) (θ : Set.Icc 0 events[k.val].angle) :
        0 < ((((R.openingPrefix events k.val).hingeSweepDirection events[k.val].hinge
          (R.openingPrefix_direction_ne_zero events k.val nonzero) events[k.val].angle
          (fun ψ bounds => sweeps k ⟨ψ, bounds⟩) r hr θ /
            R.circleDirection outward nonzero r hr : Circle) : ℂ)).re := by
      unfold hingeSweepDirection
      exact R.circleDirection_div_re_pos_of_acuteCone _ start (during k θ) r hr nonzero _
    have positive := R.prefixCircleHeading_final_pos_of_halfplane events outward nonzero
      states sweeps suffix angles_positive angles_small first at_start source_hinge r hr halfplane
    rw [R.prefixCircleHeading_eq_ratio_arg] at positive
    have final := R.circleDirection_div_re_pos_of_acuteCone Q start (prefix_cone events.length)
      r hr nonzero direction_ne_zero
    rw [Circle.coe_div] at final
    change 0 < (R.twoBankRatio Q outward nonzero (states events.length) direction_ne_zero r).re at final
    have small := Complex.arg_lt_pi_iff.mpr (Or.inl final.le)
    have identity := Complex.norm_mul_sin_arg
      (R.twoBankRatio Q outward nonzero (states events.length) direction_ne_zero r)
    rw [R.norm_twoBankRatio _ outward nonzero (states events.length) direction_ne_zero r hr,
      one_mul] at identity
    exact identity ▸ Real.sin_pos_of_pos_of_lt_pi positive small
  have gap : OrientedBankGap R Q :=
    ⟨outward, nonzero, states events.length, direction_ne_zero,
      phase, R.openingPrefix_start events events.length⟩
  simpa only [Q, openingPrefix, List.take_length] using gap

end Unfoldings.PolygonalRay
