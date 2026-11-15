module

public import Unfoldings.Geometry.OpeningAllAnchors
public import Unfoldings.Geometry.OpeningGapSeparation

/-! Construct nonoverlapping actual positive hinge-gap families from original subhistory margins. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- Original quantitative subhistory bounds construct all intermediate radial tests and prove
nonoverlap of the actual successive gaps, including their infinite ends. -/
theorem exists_nonoverlapping_positive_opening_gaps
    (events : List (Opening n)) (nonzero : R.direction ≠ 0)
    (γ : ℝ≥0) (positive : 0 < γ) (small : γ ≤ 1) {D : ℝ} (constant : 0 ≤ D)
    (radial_budget : D * openingBudget events < (γ : ℝ))
    (circle_budget : 3 * openingBudget events < (γ : ℝ) ^ 2)
    (length_bound : ∀ (j : Fin (n + 1)) (i : Fin n) (earlier : j.val ≤ i.val),
      (R.chain.interval j.val (i.val - j.val) (by omega)).projectedLength ≤
        D * ‖R.chain.vertex i.castSucc - R.chain.vertex j‖)
    (margin : ∀ (j : Fin (n + 1)) (i : Fin n), j.val ≤ i.val →
      (γ : ℝ) * (‖R.chain.vertex i.castSucc - R.chain.vertex j‖ * ‖R.chain.edge i‖) ≤
        inner ℝ (R.chain.vertex i.castSucc - R.chain.vertex j) (R.chain.edge i))
    (tail_length : ∀ j : Fin (n + 1),
      (R.chain.interval j.val (n - j.val) (by omega)).projectedLength ≤
        D * ‖R.chain.vertex (Fin.last n) - R.chain.vertex j‖)
    (tail_margin : ∀ j : Fin (n + 1),
      (γ : ℝ) * (‖R.chain.vertex (Fin.last n) - R.chain.vertex j‖ * ‖R.direction‖) ≤
        inner ℝ (R.chain.vertex (Fin.last n) - R.chain.vertex j) R.direction)
    (angles_positive : ∀ k : Fin events.length, 0 < events[k].angle)
    (angles_small : ∀ k : Fin events.length, events[k].angle < Real.pi) :
    ∃ suffixes : ∀ k : Fin events.length,
        ((R.openingPrefix events k.val).suffix events[k].hinge).Outward,
      Pairwise (fun i j : Fin events.length =>
        Disjoint (interior (R.openingGap events nonzero suffixes i))
          (interior (R.openingGap events nonzero suffixes j))) ∧
      ∀ (i j : Fin events.length), i < j →
        Disjoint (interior (R.openingGap events nonzero suffixes i))
          (R.openingGap events nonzero suffixes j) := by
  have control (word : List (Opening n)) (lower : openingBudget word ≤ openingBudget events) :
      (R.openings word).Outward ∧ ∀ hinge, ((R.openings word).suffix hinge).Outward := by
    exact R.openings_outward_and_suffixes word constant
      ((mul_le_mul_of_nonneg_left lower constant).trans_lt radial_budget)
      length_bound margin tail_length tail_margin
  have original : R.Outward := by
    have nil_budget : openingBudget ([] : List (Opening n)) ≤ openingBudget events := by
      change 0 ≤ openingBudget events
      exact openingBudget_nonneg events
    exact (control [] nil_budget).1
  have states : ∀ k, (R.openingPrefix events k).Outward := fun k =>
    (control (events.take k) (openingBudget_take_le events k)).1
  have suffixes : ∀ k : Fin events.length,
      ((R.openingPrefix events k.val).suffix events[k].hinge).Outward := fun k =>
    (control (events.take k.val) (openingBudget_take_le events k.val)).2 events[k].hinge
  have sweeps : ∀ (k : Fin events.length) (θ : Set.Icc 0 events[k].angle),
      ((R.openingPrefix events k.val).rotateSuffix events[k].hinge θ.val).Outward := by
    intro k θ
    have actual := (control (events.take k.val ++ [⟨events[k].hinge, θ.val⟩])
      (openingBudget_take_partial_le events k θ.val θ.property)).1
    simpa only [R.openings_append_singleton, openingPrefix] using actual
  have source_margin : ∀ i, (γ : ℝ) *
      (‖R.chain.vertex i.castSucc - R.start‖ * ‖R.chain.edge i‖) ≤
        inner ℝ (R.chain.vertex i.castSucc - R.start) (R.chain.edge i) :=
    fun i => margin 0 i (Nat.zero_le _)
  have source_tail : (γ : ℝ) *
      (‖R.chain.vertex (Fin.last n) - R.start‖ * ‖R.direction‖) ≤
        inner ℝ (R.chain.vertex (Fin.last n) - R.start) R.direction := tail_margin 0
  refine ⟨suffixes, ?_, ?_⟩
  · exact R.openingGaps_pairwise_disjoint_interiors events nonzero suffixes original states
      γ positive small circle_budget source_margin source_tail sweeps angles_positive angles_small
  · intro i j before
    exact R.openingGap_interior_disjoint_later events nonzero suffixes original states
      γ positive small circle_budget source_margin source_tail sweeps angles_positive angles_small
      i j before

end Unfoldings.PolygonalRay
