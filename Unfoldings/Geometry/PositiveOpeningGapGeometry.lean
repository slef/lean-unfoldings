module

public import Unfoldings.Geometry.OrientedBankGap
public import Unfoldings.Geometry.PositiveOpeningMarginGap
public import Unfoldings.Geometry.TerminalEdgeRay

/-! Opening estimates construct canonical occupied gap geometry, retaining its original side. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- Original trace controls derive both radial banks and the positive occupied gap phase. -/
theorem orientedGap_openings_of_controls
    (events : List (Opening n)) (nonzero : R.direction ≠ 0)
    (γ : ℝ≥0) (positive : 0 < γ) (small : γ ≤ 1) {D : ℝ} (constant : 0 ≤ D)
    (radial_budget : D * openingBudget events < (γ : ℝ))
    (circle_budget : 3 * openingBudget events < (γ : ℝ) ^ 2)
    (length_bound : ∀ (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val),
      (R.chain.interval j.val (i.val - j.val) (interval_between_fits j i earlier)).projectedLength ≤
        D * ‖R.chain.vertex i.castSucc - R.chain.vertex j‖)
    (margin : ∀ (j : Fin (n + 1)) (i : Fin n), j.val ≤ i.val →
      (γ : ℝ) * (‖R.chain.vertex i.castSucc - R.chain.vertex j‖ * ‖R.chain.edge i‖) ≤
        inner ℝ (R.chain.vertex i.castSucc - R.chain.vertex j) (R.chain.edge i))
    (tail_length : ∀ j : Fin (n + 1),
      (R.chain.interval j.val (n - j.val) (interval_tail_fits j)).projectedLength ≤
        D * ‖R.chain.vertex (Fin.last n) - R.chain.vertex j‖)
    (tail_margin : ∀ j : Fin (n + 1),
      (γ : ℝ) * (‖R.chain.vertex (Fin.last n) - R.chain.vertex j‖ * ‖R.direction‖) ≤
        inner ℝ (R.chain.vertex (Fin.last n) - R.chain.vertex j) R.direction)
    (angles_positive : ∀ k : Fin events.length, 0 < events[k].angle)
    (angles_small : ∀ k : Fin events.length, events[k].angle < Real.pi)
    (first : Fin events.length) (at_start : first.val = 0)
    (source_hinge : events[first].hinge = 0) :
    OrientedBankGap R (R.openings events) := by
  obtain ⟨outward, states, sweeps, suffixes⟩ := R.opening_trace_radial_controls events constant
    radial_budget length_bound margin tail_length tail_margin
  have source_margin : ∀ i, (γ : ℝ) *
      (‖R.chain.vertex i.castSucc - R.start‖ * ‖R.chain.edge i‖) ≤
        inner ℝ (R.chain.vertex i.castSucc - R.start) (R.chain.edge i) :=
    fun i => margin 0 i (Nat.zero_le _)
  have source_tail : (γ : ℝ) *
      (‖R.chain.vertex (Fin.last n) - R.start‖ * ‖R.direction‖) ≤
        inner ℝ (R.chain.vertex (Fin.last n) - R.start) R.direction := tail_margin 0
  let Q := R.openingPrefix events events.length
  have last_nonzero : Q.direction ≠ 0 := R.openingPrefix_direction_ne_zero events _ nonzero
  have phase : ∀ r : ℝ≥0, 0 < r →
      0 < (R.twoBankRatio Q outward nonzero (states events.length) last_nonzero r).im := by
    intro r radius_positive
    exact R.openingTrace_final_positive_phase events outward nonzero states γ positive small
      circle_budget source_margin source_tail sweeps suffixes angles_positive angles_small
      first at_start source_hinge r radius_positive
  have common : Q.start = R.start := R.openingPrefix_start events _
  have result : OrientedBankGap R Q := {
    first_outward := outward
    first_nonzero := nonzero
    second_outward := states events.length
    second_nonzero := last_nonzero
    phase := phase
    common := common }
  simpa only [Q, openingPrefix, List.take_length] using result

/-- All lengths and opening phases follow from the same original all-anchor margin. -/
theorem orientedGap_openings_of_margin
    (events : List (Opening n)) (nonzero : R.direction ≠ 0)
    (γ : ℝ≥0) (positive : 0 < γ) (small : γ ≤ 1)
    (circle_budget : 3 * openingBudget events < (γ : ℝ) ^ 2)
    (margin : ∀ (j : Fin (n + 1)) (i : Fin n), j.val ≤ i.val →
      (γ : ℝ) * (‖R.chain.vertex i.castSucc - R.chain.vertex j‖ * ‖R.chain.edge i‖) ≤
        inner ℝ (R.chain.vertex i.castSucc - R.chain.vertex j) (R.chain.edge i))
    (tail_margin : ∀ j : Fin (n + 1),
      (γ : ℝ) * (‖R.chain.vertex (Fin.last n) - R.chain.vertex j‖ * ‖R.direction‖) ≤
        inner ℝ (R.chain.vertex (Fin.last n) - R.chain.vertex j) R.direction)
    (angles_positive : ∀ k : Fin events.length, 0 < events[k].angle)
    (first : Fin events.length) (at_start : first.val = 0)
    (source_hinge : events[first].hinge = 0) :
    OrientedBankGap R (R.openings events) := by
  have gamma_positive : (0 : ℝ) < γ := positive
  have gamma_small : (γ : ℝ) ≤ 1 := small
  have radial_budget : (γ : ℝ)⁻¹ * openingBudget events < (γ : ℝ) := by
    have bound : openingBudget events < (γ : ℝ) * γ := by
      nlinarith [openingBudget_nonneg events]
    have estimate := mul_lt_mul_of_pos_left bound (inv_pos.mpr gamma_positive)
    rwa [← mul_assoc, inv_mul_cancel₀ gamma_positive.ne', one_mul] at estimate
  have total_small : openingBudget events < Real.pi := by
    have pi := Real.pi_gt_three
    have nonnegative : (0 : ℝ) ≤ γ := γ.coe_nonneg
    nlinarith
  have angles_small (k : Fin events.length) : events[k].angle < Real.pi :=
    (le_abs_self _).trans_lt ((opening_angle_le_budget events k).trans_lt total_small)
  exact R.orientedGap_openings_of_controls events nonzero γ positive small
    (inv_nonneg.mpr gamma_positive.le) radial_budget circle_budget
    (R.chain.subhistory_length_between gamma_positive gamma_small margin) margin
    (R.chain.subhistory_length_tail gamma_positive gamma_small margin) tail_margin
    angles_positive angles_small first at_start source_hinge

end Unfoldings.PolygonalRay

namespace Unfoldings.PolygonalChain

variable {n : ℕ} (P : PolygonalChain ℂ (n + 1))

/-- The actual terminal-edge continuation retains its canonical positive gap geometry. -/
theorem terminalEdge_orientedGap (events : List (Opening (n + 1)))
    (nonzero : P.edge (Fin.last n) ≠ 0)
    (γ : ℝ≥0) (positive : 0 < γ) (small : γ ≤ 1)
    (circle_budget : 3 * openingBudget events < (γ : ℝ) ^ 2)
    (margin : ∀ (j : Fin (n + 2)) (i : Fin (n + 1)), j.val ≤ i.val →
      (γ : ℝ) * (‖P.vertex i.castSucc - P.vertex j‖ * ‖P.edge i‖) ≤
        inner ℝ (P.vertex i.castSucc - P.vertex j) (P.edge i))
    (angles_positive : ∀ k : Fin events.length, 0 < events[k].angle)
    (first : Fin events.length) (at_start : first.val = 0)
    (source_hinge : events[first].hinge = 0) :
    OrientedBankGap P.terminalEdgeRay (P.terminalEdgeRay.openings events) :=
  P.terminalEdgeRay.orientedGap_openings_of_margin events nonzero γ positive small
    circle_budget margin (P.terminalEdgeRay_tail_margin positive.le small margin)
    angles_positive first at_start source_hinge

end Unfoldings.PolygonalChain
