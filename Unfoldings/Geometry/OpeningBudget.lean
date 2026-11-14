module

public import Unfoldings.Geometry.SuffixOpening
public import Unfoldings.Geometry.HeadingPerturbation
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Exact saved-suffix kinematics and quantitative accumulated opening budgets. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

variable {n : ℕ}

def openingBudget (events : List (Opening n)) : ℝ :=
  (events.map (fun event => |event.angle|)).sum

theorem openingBudget_nonneg (events : List (Opening n)) : 0 ≤ openingBudget events := by
  induction events with
  | nil => rfl
  | cons event events ih =>
    exact add_nonneg (abs_nonneg event.angle) ih

theorem openingHeading_oscillation (events : List (Opening n)) (i j : Fin n) :
    |openingHeading events i - openingHeading events j| ≤ openingBudget events := by
  induction events with
  | nil => simp [openingHeading, openingBudget]
  | cons event events ih =>
    let a := if event.hinge ≤ i.castSucc then event.angle else 0
    let b := if event.hinge ≤ j.castSucc then event.angle else 0
    have single : |a - b| ≤ |event.angle| := by
      dsimp [a, b]
      split_ifs <;> simp [abs_nonneg]
    change |(a + openingHeading events i) - (b + openingHeading events j)| ≤
      |event.angle| + openingBudget events
    have difference : (a + openingHeading events i) - (b + openingHeading events j) =
        (a - b) + (openingHeading events i - openingHeading events j) := by ring
    rw [difference]
    exact (abs_add_le _ _).trans (add_le_add single ih)

/-- Any sequence of actual suffix openings obeys the heading perturbation margin. -/
theorem openings_radial_margin (P : PolygonalChain ℂ n) (events : List (Opening n))
    (anchor : Fin n) {D d : ℝ} (constant : 0 ≤ D) (small : D * openingBudget events < d)
    (length_bound : P.projectedLength ≤ D * ‖P.vertex (Fin.last n) - P.vertex 0‖)
    (v : ℂ) (margin : d * (‖P.vertex (Fin.last n) - P.vertex 0‖ * ‖v‖) ≤
      inner ℝ (P.vertex (Fin.last n) - P.vertex 0) v) :
    ((d - D * openingBudget events) / (1 + D * openingBudget events)) *
      (‖(P.openings events).vertex (Fin.last n) - (P.openings events).vertex 0‖ *
        ‖polarRay (openingHeading events anchor) * v‖) ≤
      inner ℝ ((P.openings events).vertex (Fin.last n) - (P.openings events).vertex 0)
        (polarRay (openingHeading events anchor) * v) :=
  P.heading_radial_margin (P.openings events) (openingHeading events) (P.openings_edge events)
    (openingBudget_nonneg events) constant (openingHeading_oscillation events · anchor)
    small length_bound v margin

theorem openings_length_bound (P : PolygonalChain ℂ n) (events : List (Opening n))
    (anchor : Fin n) {D : ℝ} (constant : 0 ≤ D) (small : D * openingBudget events < 1)
    (length_bound : P.projectedLength ≤ D * ‖P.vertex (Fin.last n) - P.vertex 0‖) :
    (P.openings events).projectedLength ≤ (D / (1 - D * openingBudget events)) *
      ‖(P.openings events).vertex (Fin.last n) - (P.openings events).vertex 0‖ :=
  P.heading_length_bound (P.openings events) (openingHeading events) (P.openings_edge events)
    (openingBudget_nonneg events) constant (openingHeading_oscillation events · anchor)
    small length_bound

end Unfoldings.PolygonalChain
