module

public import Unfoldings.Geometry.OutwardSegmentNeighbor
public import Mathlib.Analysis.Convex.Function

/-! Local increase of a convex potential selects an incident increasing segment. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Arbitrarily near points of the prescribed set have greater potential. -/
def LocalPotentialGrowth (S : Set E) (f : E → ℝ) (p : E) : Prop :=
  ∀ ε > 0, ∃ x ∈ S, dist x p < ε ∧ f p < f x

omit [NormedSpace ℝ E] in
theorem LocalPotentialGrowth.mono {S U : Set E} {f : E → ℝ} {p : E}
    (growth : LocalPotentialGrowth S f p) (subset : S ⊆ U) :
    LocalPotentialGrowth U f p := by
  intro ε positive
  obtain ⟨x, member, close, larger⟩ := growth ε positive
  exact ⟨x, subset member, close, larger⟩

omit [NormedSpace ℝ E] in
theorem LocalPotentialGrowth.inter_open {S U : Set E} {f : E → ℝ} {p : E}
    (growth : LocalPotentialGrowth S f p) (open_U : IsOpen U) (member : p ∈ U) :
    LocalPotentialGrowth (S ∩ U) f p := by
  obtain ⟨r, positive, contains⟩ := Metric.isOpen_iff.mp open_U p member
  intro ε εpos
  obtain ⟨x, in_S, close, larger⟩ := growth (min ε r) (lt_min εpos positive)
  exact ⟨x, ⟨in_S, contains (close.trans_le (min_le_right _ _))⟩,
    close.trans_le (min_le_left _ _), larger⟩

theorem LocalPotentialGrowth.exists_increasing_segment {I : Type*} [Finite I]
    {S : Set E} {f : E → ℝ} {p : E} (growth : LocalPotentialGrowth S f p)
    (convex : ConvexOn ℝ Set.univ f) (first last : I → E)
    (cover : S ⊆ ⋃ i, segment ℝ (first i) (last i)) :
    ∃ i, p ∈ segment ℝ (first i) (last i) ∧
      (f p < f (first i) ∨ f p < f (last i)) := by
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
  obtain ⟨x, in_S, close, larger⟩ := growth ε positive
  obtain ⟨i, on_edge⟩ := Set.mem_iUnion.mp (cover in_S)
  refine ⟨i, controlled close i on_edge, ?_⟩
  by_contra neither
  have endpoints : f (first i) ≤ f p ∧ f (last i) ≤ f p := by
    simpa only [not_or, not_lt] using neither
  have sublevel : Convex ℝ {x | f x ≤ f p} := by
    simpa only [Set.mem_univ, true_and] using convex.convex_le (f p)
  exact (not_lt_of_ge (sublevel.segment_subset endpoints.1 endpoints.2 on_edge)) larger

/-- Any point before the end of a strictly increasing segment has local growth. -/
theorem localPotentialGrowth_of_segment_strict {f : E → ℝ} {a b p : E}
    (strict : StrictMonoOn (fun t : ℝ => f (AffineMap.lineMap a b t)) (Set.Icc 0 1))
    (member : p ∈ segment ℝ a b) (not_last : p ≠ b) :
    LocalPotentialGrowth (segment ℝ a b) f p := by
  obtain ⟨s, bounds, at_p⟩ := (segment_eq_image_lineMap ℝ a b).subset member
  have before : s < 1 := by
    by_contra not_before
    have equal : s = 1 := le_antisymm bounds.2 (not_lt.mp not_before)
    exact not_last (at_p.symm.trans (equal ▸ AffineMap.lineMap_apply_one a b))
  intro ε positive
  have near : ∀ᶠ r in 𝓝 s, dist (AffineMap.lineMap a b r) p < ε := by
    have continuous : Continuous (fun r : ℝ => dist (AffineMap.lineMap a b r) p) :=
      AffineMap.lineMap_continuous.dist continuous_const
    have small : dist (AffineMap.lineMap a b s) p < ε := by
      rw [at_p, dist_self]
      exact positive
    exact continuous.continuousAt.eventually_lt_const small
  have after : ∀ᶠ r in 𝓝[>] s, s < r := self_mem_nhdsWithin
  have below : ∀ᶠ r in 𝓝[>] s, r < 1 := by
    have upper : ∀ᶠ r in 𝓝 s, r < 1 := Iio_mem_nhds before
    exact upper.filter_mono nhdsWithin_le_nhds
  obtain ⟨r, close, greater, less⟩ :=
    ((near.filter_mono nhdsWithin_le_nhds).and (after.and below)).exists
  refine ⟨AffineMap.lineMap a b r, lineMap_mem_segment ℝ a b
    ⟨bounds.1.trans greater.le, less.le⟩, close, ?_⟩
  exact at_p ▸ strict bounds ⟨bounds.1.trans greater.le, less.le⟩ greater

end Unfoldings
