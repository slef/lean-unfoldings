module

public import Unfoldings.Geometry.OpeningAllAnchors
public import Unfoldings.Geometry.OpeningCircleTrace

/-! Construct every radial test for an actual opening trace from original subhistory estimates. -/

@[expose] public section

noncomputable section

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- A single original budget supplies the original bank, all prefix banks, every intermediate
angle and every current hinge suffix. -/
theorem opening_trace_radial_controls (events : List (Opening n)) {D d : ℝ}
    (constant : 0 ≤ D) (budget : D * openingBudget events < d)
    (length_bound : ∀ (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val),
      (R.chain.interval j.val (i.val - j.val) (interval_between_fits j i earlier)).projectedLength ≤
        D * ‖R.chain.vertex i.castSucc - R.chain.vertex j‖)
    (margin : ∀ (j : Fin (n + 1)) (i : Fin n), j.val ≤ i.val →
      d * (‖R.chain.vertex i.castSucc - R.chain.vertex j‖ * ‖R.chain.edge i‖) ≤
        inner ℝ (R.chain.vertex i.castSucc - R.chain.vertex j) (R.chain.edge i))
    (tail_length : ∀ j : Fin (n + 1),
      (R.chain.interval j.val (n - j.val) (interval_tail_fits j)).projectedLength ≤
        D * ‖R.chain.vertex (Fin.last n) - R.chain.vertex j‖)
    (tail_margin : ∀ j : Fin (n + 1),
      d * (‖R.chain.vertex (Fin.last n) - R.chain.vertex j‖ * ‖R.direction‖) ≤
        inner ℝ (R.chain.vertex (Fin.last n) - R.chain.vertex j) R.direction) :
    R.Outward ∧
      (∀ k, (R.openingPrefix events k).Outward) ∧
      (∀ (k : Fin events.length) (θ : Set.Icc 0 events[k].angle),
        ((R.openingPrefix events k.val).rotateSuffix events[k].hinge θ.val).Outward) ∧
      (∀ k : Fin events.length,
        ((R.openingPrefix events k.val).suffix events[k].hinge).Outward) := by
  have control (word : List (Opening n)) (lower : openingBudget word ≤ openingBudget events) :
      (R.openings word).Outward ∧ ∀ hinge, ((R.openings word).suffix hinge).Outward := by
    exact R.openings_outward_and_suffixes word constant
      ((mul_le_mul_of_nonneg_left lower constant).trans_lt budget)
      length_bound margin tail_length tail_margin
  refine ⟨?_, ?_, ?_, ?_⟩
  · have nil_budget : openingBudget ([] : List (Opening n)) ≤ openingBudget events := by
      change 0 ≤ openingBudget events
      exact openingBudget_nonneg events
    exact (control [] nil_budget).1
  · intro k
    exact (control (events.take k) (openingBudget_take_le events k)).1
  · intro k θ
    have actual := (control (events.take k.val ++ [⟨events[k].hinge, θ.val⟩])
      (openingBudget_take_partial_le events k θ.val θ.property)).1
    simpa only [R.openings_append_singleton, openingPrefix] using actual
  · intro k
    exact (control (events.take k.val) (openingBudget_take_le events k.val)).2 events[k].hinge

end Unfoldings.PolygonalRay
