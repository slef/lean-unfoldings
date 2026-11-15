module

public import Unfoldings.Geometry.OpeningCommonDirection
public import Unfoldings.Geometry.OpeningPrefixBudget
public import Unfoldings.Geometry.HingeCommonHeading
public import Unfoldings.Geometry.OpeningZero

/-! Actual prefix banks and their common-frame source-circle headings. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- The actual bank after the indicated initial segment of the opening list. -/
def openingPrefix (events : List (Opening n)) (k : ℕ) : PolygonalRay ℂ n :=
  R.openings (events.take k)

@[simp] theorem openingPrefix_start (events : List (Opening n)) (k : ℕ) :
    (R.openingPrefix events k).start = R.start := R.openings_start _

theorem openingPrefix_direction_ne_zero (events : List (Opening n)) (k : ℕ)
    (nonzero : R.direction ≠ 0) : (R.openingPrefix events k).direction ≠ 0 :=
  R.openings_direction_ne_zero _ nonzero

/-- The next prefix is exactly the current bank opened at its true current hinge. -/
theorem openingPrefix_succ (events : List (Opening n)) (k : Fin events.length) :
    R.openingPrefix events (k.val + 1) =
      (R.openingPrefix events k.val).rotateSuffix events[k].hinge events[k].angle := by
  unfold openingPrefix
  rw [← List.take_concat_get' events k.val k.isLt, R.openings_append_singleton]
  rfl

variable (events : List (Opening n)) (outward : R.Outward) (nonzero : R.direction ≠ 0)
  (states : ∀ k, (R.openingPrefix events k).Outward)

/-- Every prefix is measured against the same actual original contact. -/
def prefixCircleHeading (r : ℝ≥0) (radius_positive : 0 < r) (k : ℕ) : ℝ :=
  Complex.arg (((R.openingPrefix events k).circleDirection (states k)
    (R.openingPrefix_direction_ne_zero events k nonzero) r radius_positive /
      R.circleDirection outward nonzero r radius_positive : Circle) : ℂ)

variable (γ : ℝ≥0) (positive : 0 < γ) (small : γ ≤ 1)
  (budget : 3 * openingBudget events < (γ : ℝ) ^ 2)
  (margin : ∀ i, (γ : ℝ) * (‖R.chain.vertex i.castSucc - R.start‖ * ‖R.chain.edge i‖) ≤
    inner ℝ (R.chain.vertex i.castSucc - R.start) (R.chain.edge i))
  (tail_margin : (γ : ℝ) * (‖R.chain.vertex (Fin.last n) - R.start‖ * ‖R.direction‖) ≤
    inner ℝ (R.chain.vertex (Fin.last n) - R.start) R.direction)
  (sweeps : ∀ (k : Fin events.length) (θ : Set.Icc 0 events[k].angle),
    ((R.openingPrefix events k.val).rotateSuffix events[k].hinge θ.val).Outward)

include outward nonzero positive small budget margin tail_margin sweeps in
/-- The global budget supplies the common halfplane at every actual intermediate angle. -/
theorem openingPrefix_sweep_halfplane (k : Fin events.length) (r : ℝ≥0)
    (radius_positive : 0 < r) (θ : Set.Icc 0 events[k].angle) :
    0 < ((((R.openingPrefix events k.val).hingeSweepDirection events[k].hinge
      (R.openingPrefix_direction_ne_zero events k.val nonzero) events[k].angle
      (fun ψ bounds => sweeps k ⟨ψ, bounds⟩) r radius_positive θ /
        R.circleDirection outward nonzero r radius_positive : Circle) : ℂ)).re := by
  let partialEvents : List (Opening n) := events.take k.val ++ [⟨events[k].hinge, θ.val⟩]
  have partial_outward : (R.openings partialEvents).Outward := by
    rw [show partialEvents = events.take k.val ++ [⟨events[k].hinge, θ.val⟩] from rfl,
      R.openings_append_singleton]
    exact sweeps k θ
  have partial_budget : 3 * openingBudget partialEvents < (γ : ℝ) ^ 2 := by
    have lower := openingBudget_take_partial_le events k θ.val θ.property
    exact (mul_le_mul_of_nonneg_left lower (by norm_num)).trans_lt budget
  have control := R.openings_circleDirection_halfplane outward nonzero partialEvents partial_outward
    γ positive small partial_budget margin tail_margin r radius_positive
  simpa only [partialEvents, R.openings_append_singleton, openingPrefix,
    hingeSweepDirection] using control

variable (suffixes : ∀ k : Fin events.length,
    ((R.openingPrefix events k.val).suffix events[k].hinge).Outward)
  (angles_positive : ∀ k : Fin events.length, 0 < events[k].angle)
  (angles_small : ∀ k : Fin events.length, events[k].angle < Real.pi)

include outward nonzero states positive small budget margin tail_margin sweeps suffixes
  angles_positive angles_small in
/-- Consecutive actual banks are ordered in the same real angular coordinate. -/
theorem prefixCircleHeading_step (r : ℝ≥0) (radius_positive : 0 < r) (k : Fin events.length) :
    R.prefixCircleHeading events outward nonzero states r radius_positive k.val ≤
      R.prefixCircleHeading events outward nonzero states r radius_positive (k.val + 1) := by
  have ordered := (R.openingPrefix events k.val).monotone_hingeCommonHeading events[k].hinge
    (R.openingPrefix_direction_ne_zero events k.val nonzero) events[k].angle
    (fun ψ bounds => sweeps k ⟨ψ, bounds⟩) r radius_positive
    (R.circleDirection outward nonzero r radius_positive) (states k.val) (suffixes k)
    (angles_positive k) (angles_small k)
    (R.openingPrefix_sweep_halfplane events outward nonzero γ positive small budget margin
      tail_margin sweeps k r radius_positive)
  have bound := ordered (show
    (⟨0, le_rfl, (angles_positive k).le⟩ : Set.Icc 0 events[k].angle) ≤
      ⟨events[k].angle, (angles_positive k).le, le_rfl⟩ from (angles_positive k).le)
  simpa only [hingeCommonHeading, hingeSweepDirection, rotateSuffix_zero,
    prefixCircleHeading, Circle.coe_div, ← R.openingPrefix_succ events k] using bound

include outward nonzero states positive small budget margin tail_margin sweeps suffixes
  angles_positive angles_small in
/-- Source-circle headings of all actual prefix banks form one monotone finite sequence. -/
theorem monotone_prefixCircleHeading (r : ℝ≥0) (radius_positive : 0 < r) :
    Monotone (fun k : Fin (events.length + 1) =>
      R.prefixCircleHeading events outward nonzero states r radius_positive k.val) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro k
  exact R.prefixCircleHeading_step events outward nonzero states γ positive small budget
    margin tail_margin sweeps suffixes angles_positive angles_small r radius_positive k

end Unfoldings.PolygonalRay
