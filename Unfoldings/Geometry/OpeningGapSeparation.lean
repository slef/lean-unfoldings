module

public import Unfoldings.Geometry.OpeningCircleTrace
public import Unfoldings.Geometry.HingeGapHeadingBounds

/-! Disjoint interiors of actual successive positive hinge gaps under a uniform radial budget. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n) (events : List (Opening n))

/-- The literal gap added at this event, with its actual current hinge and infinite banks. -/
def openingGap (nonzero : R.direction ≠ 0)
    (suffixes : ∀ k : Fin events.length,
      ((R.openingPrefix events k.val).suffix events[k].hinge).Outward)
    (k : Fin events.length) : Set ℂ :=
  ((R.openingPrefix events k.val).suffix events[k].hinge).rotationGap (suffixes k)
    (R.openingPrefix_direction_ne_zero events k.val nonzero) events[k].angle

variable (nonzero : R.direction ≠ 0)
  (suffixes : ∀ k : Fin events.length,
    ((R.openingPrefix events k.val).suffix events[k].hinge).Outward)
  (outward : R.Outward)
  (states : ∀ k, (R.openingPrefix events k).Outward)
  (γ : ℝ≥0) (positive : 0 < γ) (small : γ ≤ 1)
  (budget : 3 * openingBudget events < (γ : ℝ) ^ 2)
  (margin : ∀ i, (γ : ℝ) * (‖R.chain.vertex i.castSucc - R.start‖ * ‖R.chain.edge i‖) ≤
    inner ℝ (R.chain.vertex i.castSucc - R.start) (R.chain.edge i))
  (tail_margin : (γ : ℝ) * (‖R.chain.vertex (Fin.last n) - R.start‖ * ‖R.direction‖) ≤
    inner ℝ (R.chain.vertex (Fin.last n) - R.start) R.direction)
  (sweeps : ∀ (k : Fin events.length) (θ : Set.Icc 0 events[k].angle),
    ((R.openingPrefix events k.val).rotateSuffix events[k].hinge θ.val).Outward)
  (angles_positive : ∀ k : Fin events.length, 0 < events[k].angle)
  (angles_small : ∀ k : Fin events.length, events[k].angle < Real.pi)

/-- Point headings use the original source, original circle and original bank reference. -/
def openingPointHeading (r : ℝ≥0) (radius_positive : 0 < r) (z : ℂ) : ℝ :=
  Complex.arg ((z - R.start) / (r : ℂ) /
    (R.circleDirection outward nonzero r radius_positive : ℂ))

include outward states positive small budget margin tail_margin sweeps
  angles_positive angles_small in
/-- Every actual gap point is between its consecutive prefix banks in angular order. -/
theorem openingGap_heading_bounds (k : Fin events.length) (r : ℝ≥0) (radius_positive : 0 < r)
    {z : ℂ} (member : z ∈ R.openingGap events nonzero suffixes k)
    (radius : dist R.start z = (r : ℝ)) :
    R.openingPointHeading nonzero outward r radius_positive z ∈
      Set.Icc (R.prefixCircleHeading events outward nonzero states r radius_positive k.val)
        (R.prefixCircleHeading events outward nonzero states r radius_positive (k.val + 1)) := by
  have bound := (R.openingPrefix events k.val).hingeGap_heading_bounds events[k].hinge
    (R.openingPrefix_direction_ne_zero events k.val nonzero) events[k].angle
    (fun ψ bounds => sweeps k ⟨ψ, bounds⟩) r radius_positive
    (R.circleDirection outward nonzero r radius_positive) (states k.val) (suffixes k)
    (angles_positive k) (angles_small k)
    (R.openingPrefix_sweep_halfplane events outward nonzero γ positive small budget margin
      tail_margin sweeps k r radius_positive) member
    (by rwa [R.openingPrefix_start])
  simpa only [openingPointHeading, R.openingPrefix_start, hingeCommonHeading,
    hingeSweepDirection, rotateSuffix_zero, prefixCircleHeading, Circle.coe_div,
    ← R.openingPrefix_succ events k] using bound

include outward states positive small budget margin tail_margin sweeps
  angles_positive angles_small in
/-- Interior points lie strictly inside their actual bank-heading interval. -/
theorem openingGap_interior_heading_bounds (k : Fin events.length) (r : ℝ≥0)
    (radius_positive : 0 < r) {z : ℂ}
    (member : z ∈ interior (R.openingGap events nonzero suffixes k))
    (radius : dist R.start z = (r : ℝ)) :
    R.openingPointHeading nonzero outward r radius_positive z ∈
      Set.Ioo (R.prefixCircleHeading events outward nonzero states r radius_positive k.val)
        (R.prefixCircleHeading events outward nonzero states r radius_positive (k.val + 1)) := by
  have bound := (R.openingPrefix events k.val).hingeGap_interior_heading_bounds events[k].hinge
    (R.openingPrefix_direction_ne_zero events k.val nonzero) events[k].angle
    (fun ψ bounds => sweeps k ⟨ψ, bounds⟩) r radius_positive
    (R.circleDirection outward nonzero r radius_positive) (suffixes k)
    (angles_positive k) (angles_small k)
    (R.openingPrefix_sweep_halfplane events outward nonzero γ positive small budget margin
      tail_margin sweeps k r radius_positive) member
    (by rwa [R.openingPrefix_start])
  simpa only [openingPointHeading, R.openingPrefix_start, hingeCommonHeading,
    hingeSweepDirection, rotateSuffix_zero, prefixCircleHeading, Circle.coe_div,
    ← R.openingPrefix_succ events k] using bound

include sweeps angles_positive angles_small in
theorem openingGap_interior_ne_source (k : Fin events.length) {z : ℂ}
    (member : z ∈ interior (R.openingGap events nonzero suffixes k)) : z ≠ R.start := by
  intro equal
  have above := (R.openingPrefix events k.val).hingeGap_interior_radius_gt_hinge events[k].hinge
    (R.openingPrefix_direction_ne_zero events k.val nonzero) events[k].angle
    (fun ψ bounds => sweeps k ⟨ψ, bounds⟩) (suffixes k) (angles_positive k) (angles_small k) member
  rw [R.openingPrefix_start, equal, dist_self] at above
  exact (not_lt_of_ge dist_nonneg) above

include outward states positive small budget margin tail_margin sweeps
  angles_positive angles_small in
/-- No earlier gap interior meets any later closed gap. Boundary contact remains allowed. -/
theorem openingGap_interior_disjoint_later (i j : Fin events.length) (before : i < j) :
    Disjoint (interior (R.openingGap events nonzero suffixes i))
      (R.openingGap events nonzero suffixes j) := by
  apply Set.disjoint_left.mpr
  intro z first last
  let r := nndist R.start z
  have radius_positive : 0 < r := by
    exact (show (0 : ℝ) < dist R.start z from dist_pos.mpr
      (R.openingGap_interior_ne_source events nonzero suffixes sweeps
        angles_positive angles_small i first).symm)
  have first_bound := R.openingGap_interior_heading_bounds events nonzero suffixes outward states
    γ positive small budget margin tail_margin sweeps angles_positive angles_small
    i r radius_positive first rfl
  have last_bound := R.openingGap_heading_bounds events nonzero suffixes outward states
    γ positive small budget margin tail_margin sweeps angles_positive angles_small
    j r radius_positive last rfl
  have ordered := R.monotone_prefixCircleHeading events outward nonzero states γ positive small
    budget margin tail_margin sweeps suffixes angles_positive angles_small r radius_positive
    (show i.succ ≤ j.castSucc by change i.val + 1 ≤ j.val; exact before)
  exact (not_lt_of_ge last_bound.1) (first_bound.2.trans_le ordered)

include outward states positive small budget margin tail_margin sweeps
  angles_positive angles_small in
/-- Actual finite positive hinge gaps have pairwise disjoint interiors. -/
theorem openingGaps_pairwise_disjoint_interiors :
    Pairwise (fun i j : Fin events.length =>
      Disjoint (interior (R.openingGap events nonzero suffixes i))
        (interior (R.openingGap events nonzero suffixes j))) := by
  intro i j different
  rcases lt_or_gt_of_ne different with before | before
  · exact Disjoint.mono_right interior_subset
      (R.openingGap_interior_disjoint_later events nonzero suffixes outward states
        γ positive small budget margin tail_margin sweeps angles_positive angles_small i j before)
  · exact (Disjoint.mono_right interior_subset
      (R.openingGap_interior_disjoint_later events nonzero suffixes outward states
        γ positive small budget margin tail_margin sweeps angles_positive angles_small
        j i before)).symm

end Unfoldings.PolygonalRay
