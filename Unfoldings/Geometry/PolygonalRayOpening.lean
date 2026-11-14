module

public import Unfoldings.Geometry.PolygonalRayEmbedding
public import Unfoldings.Geometry.OpeningBudget
public import Unfoldings.Geometry.HeadingRadialChain

/-! Actual bank openings rotate the entire infinite suffix, including its straight tail. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings
namespace PolygonalChain

variable {n : ℕ}

def openingTailHeading (events : List (Opening n)) : ℝ :=
  (events.map Opening.angle).sum

theorem openingHeading_tail_error (events : List (Opening n)) (i : Fin n) :
    |openingHeading events i - openingTailHeading events| ≤ openingBudget events := by
  induction events with
  | nil => simp [openingHeading, openingTailHeading, openingBudget]
  | cons event events ih =>
    let a := if event.hinge ≤ i.castSucc then event.angle else 0
    have single : |a - event.angle| ≤ |event.angle| := by
      dsimp [a]
      split_ifs <;> simp [abs_nonneg]
    change |(a + openingHeading events i) - (event.angle + openingTailHeading events)| ≤
      |event.angle| + openingBudget events
    have difference : (a + openingHeading events i) - (event.angle + openingTailHeading events) =
        (a - event.angle) + (openingHeading events i - openingTailHeading events) := by ring
    rw [difference]
    exact (abs_add_le _ _).trans (add_le_add single ih)

end PolygonalChain

namespace PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n)

def rotateSuffix (hinge : Fin (n + 1)) (angle : ℝ) : PolygonalRay ℂ n where
  chain := R.chain.rotateSuffix hinge angle
  direction := complexRotation angle R.direction

@[simp] theorem rotateSuffix_start (hinge : Fin (n + 1)) (angle : ℝ) :
    (R.rotateSuffix hinge angle).start = R.start := R.chain.rotateSuffix_start hinge angle

/-- The tail is moved with the current hinge translation; it is not replaced by a parallel ray. -/
theorem rotateSuffix_tail (hinge : Fin (n + 1)) (angle : ℝ) (t : ℝ≥0) :
    (R.rotateSuffix hinge angle).tail t =
      R.chain.vertex hinge + complexRotation angle (R.tail t - R.chain.vertex hinge) := by
  change (R.chain.rotateSuffix hinge angle).vertex (Fin.last n) +
    (t : ℝ) • complexRotation angle R.direction = _
  rw [R.chain.rotateSuffix_vertex_ge hinge angle (Fin.last n) (Fin.le_last _)]
  simp only [tail, map_sub, map_add, map_smul]
  abel

def openings (events : List (Opening n)) : PolygonalRay ℂ n :=
  events.foldl (fun Q event => Q.rotateSuffix event.hinge event.angle) R

@[simp] theorem openings_chain (events : List (Opening n)) :
    (R.openings events).chain = R.chain.openings events := by
  induction events generalizing R with
  | nil => rfl
  | cons event events ih => exact ih (R.rotateSuffix event.hinge event.angle)

@[simp] theorem openings_start (events : List (Opening n)) :
    (R.openings events).start = R.start := by
  induction events generalizing R with
  | nil => rfl
  | cons event events ih =>
    change ((R.rotateSuffix event.hinge event.angle).openings events).start = _
    rw [ih, R.rotateSuffix_start]

theorem openings_direction (events : List (Opening n)) :
    (R.openings events).direction = polarRay (openingTailHeading events) * R.direction := by
  induction events generalizing R with
  | nil => simp [openings, openingTailHeading]
  | cons event events ih =>
    change ((R.rotateSuffix event.hinge event.angle).openings events).direction = _
    rw [ih]
    simp only [rotateSuffix, complexRotation_apply, openingTailHeading, List.map_cons,
      List.sum_cons, polarRay_add]
    ring

theorem openings_direction_ne_zero (events : List (Opening n)) (nonzero : R.direction ≠ 0) :
    (R.openings events).direction ≠ 0 := by
  rw [R.openings_direction]
  exact mul_ne_zero (polarRay_ne_zero _) nonzero

/-- All source-radial tests survive a sufficiently small sequence of actual bank openings. -/
theorem openings_outward (events : List (Opening n)) {D d : ℝ} (constant : 0 ≤ D)
    (small : D * openingBudget events < d)
    (interval_length : ∀ (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val),
      (R.chain.interval j.val (i.val - j.val) (by omega)).projectedLength ≤
        D * ‖R.chain.vertex i.castSucc - R.chain.vertex j‖)
    (margin : ∀ (j : Fin (n + 1)) (i : Fin n), j.val ≤ i.val →
      d * (‖R.chain.vertex i.castSucc - R.chain.vertex j‖ * ‖R.chain.edge i‖) ≤
        inner ℝ (R.chain.vertex i.castSucc - R.chain.vertex j) (R.chain.edge i))
    (length_bound : R.chain.projectedLength ≤
      D * ‖R.chain.vertex (Fin.last n) - R.chain.vertex 0‖)
    (tail_margin : d * (‖R.chain.vertex (Fin.last n) - R.start‖ * ‖R.direction‖) ≤
      inner ℝ (R.chain.vertex (Fin.last n) - R.start) R.direction) :
    (R.openings events).Outward := by
  have finite := R.chain.outward_of_heading_oscillation (R.chain.openings events)
    (openingHeading events) (R.chain.openings_edge events) (openingBudget_nonneg events)
    constant small (openingHeading_oscillation events) interval_length margin
  constructor
  · intro i _
    change Monotone (fun t : unitInterval =>
      dist (R.openings events).start ((R.openings events).chain.point i t))
    unfold start
    rw [R.openings_chain]
    exact ((R.chain.openings events).radiallyMonotone_iff_outward.mpr finite) 0 i (Nat.zero_le _)
  · have estimate := R.chain.heading_radial_margin (R.chain.openings events)
      (openingHeading events) (R.chain.openings_edge events) (openingBudget_nonneg events)
      constant (openingHeading_tail_error events) small length_bound R.direction tail_margin
    rw [← R.openings_chain, ← R.openings_direction] at estimate
    have coefficient : 0 ≤ (d - D * openingBudget events) / (1 + D * openingBudget events) :=
      div_nonneg (sub_pos.mpr small).le (by nlinarith [openingBudget_nonneg events])
    exact (mul_nonneg coefficient (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans estimate

end PolygonalRay
end Unfoldings
