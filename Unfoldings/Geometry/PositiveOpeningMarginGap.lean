module

public import Unfoldings.Geometry.PositiveOpeningTraceGap
public import Unfoldings.Geometry.RadialSubhistoryLength
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Radial margins alone supply all geometric length data for complete positive opening gaps. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- Every individual event is charged to the total absolute opening budget. -/
theorem opening_angle_le_budget (events : List (Opening n)) (k : Fin events.length) :
    |events[k].angle| ≤ openingBudget events := by
  have split : events.take (k.val + 1) = events.take k.val ++ [events[k]] :=
    (List.take_concat_get' events k.val k.isLt).symm
  calc
    _ ≤ openingBudget (events.take k.val) + |events[k].angle| :=
      le_add_of_nonneg_left (openingBudget_nonneg _)
    _ = openingBudget (events.take (k.val + 1)) := by
      rw [split, openingBudget_append, openingBudget_singleton]
    _ ≤ openingBudget events := openingBudget_take_le events _

/-- No length certificates are supplied: all opening-trace lengths follow from the same margin. -/
theorem exists_positive_opening_trace_gap_of_margin
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
    ∃ G : Set ℂ,
      IsClosed G ∧ frontier G = R.carrier ∪ (R.openings events).carrier ∧
      R.carrier ∩ (R.openings events).carrier = {R.start} ∧
      (interior G).Nonempty ∧ closure (interior G) = G ∧
      CompleteSpace (PolygonalPoint G) ∧ ContractibleSpace (PolygonalPoint G) ∧
      ∃ (I : Type) (_ : Fintype I) (cells : I → Set ℂ),
        (∀ i, IsClosed (cells i) ∧ Convex ℝ (cells i) ∧ (interior (cells i)).Nonempty) ∧
        (∀ i j, i ≠ j → Disjoint (interior (cells i)) (interior (cells j))) ∧
        G = ⋃ i, cells i := by
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
  exact R.exists_positive_opening_trace_gap events nonzero γ positive small
    (inv_nonneg.mpr gamma_positive.le) radial_budget circle_budget
    (R.chain.subhistory_length_between gamma_positive gamma_small margin) margin
    (R.chain.subhistory_length_tail gamma_positive gamma_small margin) tail_margin
    angles_positive angles_small first at_start source_hinge

end Unfoldings.PolygonalRay
