module

public import Unfoldings.Geometry.LocalRadialGrowth
public import Mathlib.Analysis.Normed.Module.Convex

/-! Local outward progress on a finite segment cover gives an outward incident segment. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite I]

/-- A finite geometric edge cover turns arbitrarily near radial progress into an incident edge
with a strictly farther endpoint. This includes vertices on the boundary of the covered set. -/
theorem LocalRadialGrowth.exists_outward_segment {S : Set E} {q p : E}
    (growth : LocalRadialGrowth S q p) (first last : I → E)
    (cover : S ⊆ ⋃ i, segment ℝ (first i) (last i)) :
    ∃ i, p ∈ segment ℝ (first i) (last i) ∧
      (dist q p < dist q (first i) ∨ dist q p < dist q (last i)) := by
  have exclude (i : I) : ∀ᶠ x in 𝓝 p,
      x ∈ segment ℝ (first i) (last i) → p ∈ segment ℝ (first i) (last i) := by
    by_cases member : p ∈ segment ℝ (first i) (last i)
    · exact Eventually.of_forall (fun _ _ => member)
    · have compact : IsCompact (segment ℝ (first i) (last i)) := by
        rw [segment_eq_image_lineMap]
        exact isCompact_Icc.image AffineMap.lineMap_continuous
      filter_upwards [compact.isClosed.isOpen_compl.mem_nhds member] with x outside
      exact fun inside => (outside inside).elim
  obtain ⟨ε, positive, controlled⟩ :=
    Metric.eventually_nhds_iff.mp (Filter.eventually_all.mpr exclude)
  obtain ⟨x, in_S, close, farther⟩ := growth ε positive
  obtain ⟨i, on_edge⟩ := Set.mem_iUnion.mp (cover in_S)
  refine ⟨i, controlled close i on_edge, ?_⟩
  by_contra neither
  have endpoints : dist q (first i) ≤ dist q p ∧ dist q (last i) ≤ dist q p := by
    simpa only [not_or, not_lt] using neither
  have first_in : first i ∈ Metric.closedBall q (dist q p) := by
    simpa only [Metric.mem_closedBall, dist_comm] using endpoints.1
  have last_in : last i ∈ Metric.closedBall q (dist q p) := by
    simpa only [Metric.mem_closedBall, dist_comm] using endpoints.2
  have bounded := (convex_closedBall q (dist q p)).segment_subset first_in last_in on_edge
  have distance : dist q x ≤ dist q p := by
    simpa only [Metric.mem_closedBall, dist_comm] using bounded
  exact (not_lt_of_ge distance) farther

end Unfoldings
