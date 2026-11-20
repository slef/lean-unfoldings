module

public import Unfoldings.Geometry.OpeningTraceControl
public import Unfoldings.Geometry.OpeningTracePositivePhase
public import Unfoldings.Geometry.TwoBankGapMetric

/-! Construct complete actual polygonal Jordan gaps for positive source-opening traces. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.PolygonalRay

open PolygonalChain

variable {n : ℕ} (R : PolygonalRay ℂ n)

/-- A strictly positive relative phase supplies a complete polygonal gap between two actual
source-radial banks with the same source. -/
theorem exists_twoBankGap_of_positive_phase {m : ℕ} (Q : PolygonalRay ℂ m)
    (outward : R.Outward) (nonzero : R.direction ≠ 0)
    (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
    (common : Q.start = R.start)
    (phase : ∀ r : ℝ≥0, 0 < r → 0 < (R.twoBankRatio Q outward nonzero
      last_outward last_nonzero r).im) :
    ∃ G : Set ℂ,
      IsClosed G ∧ frontier G = R.carrier ∪ Q.carrier ∧
      R.carrier ∩ Q.carrier = {R.start} ∧
      (interior G).Nonempty ∧ closure (interior G) = G ∧
      CompleteSpace (PolygonalPoint G) ∧ ContractibleSpace (PolygonalPoint G) ∧
      ∃ (I : Type) (_ : Fintype I) (cells : I → Set ℂ),
        (∀ i, IsClosed (cells i) ∧ Convex ℝ (cells i) ∧ (interior (cells i)).Nonempty) ∧
        (∀ i j, i ≠ j → Disjoint (interior (cells i)) (interior (cells j))) ∧
        G = ⋃ i, cells i := by
  exact ⟨R.twoBankGap Q outward nonzero last_outward last_nonzero phase,
    R.isClosed_twoBankGap Q outward nonzero last_outward last_nonzero phase,
    R.frontier_twoBankGap Q outward nonzero last_outward last_nonzero phase common,
    R.twoBank_carriers_inter Q outward nonzero last_outward last_nonzero phase common,
    R.twoBankGap_interior_nonempty Q outward nonzero last_outward last_nonzero phase,
    R.twoBankGap_regular_closed Q outward nonzero last_outward last_nonzero phase,
    R.twoBankGap_complete Q outward nonzero last_outward last_nonzero phase common,
    R.twoBankGap_contractible Q outward nonzero last_outward last_nonzero phase common,
    R.exists_twoBankGap_cell_cover Q outward nonzero last_outward last_nonzero phase common⟩

/-- Original subhistory estimates and a positive first opening at the source construct a complete
polygonal Jordan gap between the exact original and final banks, including their infinite tails. -/
theorem exists_positive_opening_trace_gap
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
    ∃ G : Set ℂ,
      IsClosed G ∧ frontier G = R.carrier ∪ (R.openings events).carrier ∧
      R.carrier ∩ (R.openings events).carrier = {R.start} ∧
      (interior G).Nonempty ∧ closure (interior G) = G ∧
      CompleteSpace (PolygonalPoint G) ∧ ContractibleSpace (PolygonalPoint G) ∧
      ∃ (I : Type) (_ : Fintype I) (cells : I → Set ℂ),
        (∀ i, IsClosed (cells i) ∧ Convex ℝ (cells i) ∧ (interior (cells i)).Nonempty) ∧
        (∀ i j, i ≠ j → Disjoint (interior (cells i)) (interior (cells j))) ∧
        G = ⋃ i, cells i := by
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
  simpa only [Q, openingPrefix, List.take_length] using
    R.exists_twoBankGap_of_positive_phase Q outward nonzero (states events.length)
      last_nonzero common phase

end Unfoldings.PolygonalRay
