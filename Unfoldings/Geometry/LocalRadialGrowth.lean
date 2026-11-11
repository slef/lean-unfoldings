module

public import Unfoldings.Geometry.ClippedRadialTails
public import Unfoldings.Geometry.RadialSegment

/-! Arbitrarily near outward progress on actual whole radial segments. -/

@[expose] public section

noncomputable section

open Filter Topology

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def LocalRadialGrowth (S : Set E) (q p : E) : Prop :=
  ∀ ε > 0, ∃ x ∈ S, dist x p < ε ∧ dist q p < dist q x

omit [NormedSpace ℝ E] in
theorem LocalRadialGrowth.mono {S U : Set E} {q p : E} (growth : LocalRadialGrowth S q p)
    (subset : S ⊆ U) : LocalRadialGrowth U q p := by
  intro ε positive
  obtain ⟨x, member, close, farther⟩ := growth ε positive
  exact ⟨x, subset member, close, farther⟩

omit [NormedSpace ℝ E] in
theorem LocalRadialGrowth.inter_open {S U : Set E} {q p : E}
    (growth : LocalRadialGrowth S q p) (open_U : IsOpen U) (member : p ∈ U) :
    LocalRadialGrowth (S ∩ U) q p := by
  obtain ⟨r, positive, contains⟩ := Metric.isOpen_iff.mp open_U p member
  intro ε εpos
  obtain ⟨x, in_S, close, farther⟩ := growth (min ε r) (lt_min εpos positive)
  exact ⟨x, ⟨in_S, contains (close.trans_le (min_le_right _ _))⟩,
    close.trans_le (min_le_left _ _), farther⟩

/-- A nonterminal point of a strictly radially increasing segment has arbitrary near progress. -/
theorem localRadialGrowth_of_segment_strict {a b q p : E}
    (strict : ∀ {s r : ℝ}, 0 ≤ s → s < r →
      dist q (AffineMap.lineMap a b s) < dist q (AffineMap.lineMap a b r))
    (member : p ∈ segment ℝ a b) (not_last : p ≠ b) :
    LocalRadialGrowth (segment ℝ a b) q p := by
  obtain ⟨s, bounds, at_p⟩ := (segment_eq_image_lineMap ℝ a b).subset member
  have before : s < 1 := by
    by_contra not_before
    have equal : s = 1 := le_antisymm bounds.2 (not_lt.mp not_before)
    exact not_last (at_p.symm.trans (equal ▸ AffineMap.lineMap_apply_one a b))
  intro ε positive
  have near : ∀ᶠ r in 𝓝 s, dist (AffineMap.lineMap a b r) p < ε := by
    have continuous : Continuous (fun r : ℝ => dist (AffineMap.lineMap a b r) p) :=
      AffineMap.lineMap_continuous.dist continuous_const
    have at_zero : dist (AffineMap.lineMap a b s) p < ε := by
      rw [at_p, dist_self]
      exact positive
    exact continuous.continuousAt.eventually_lt_const at_zero
  have after : ∀ᶠ r in 𝓝[>] s, s < r := self_mem_nhdsWithin
  have below : ∀ᶠ r in 𝓝[>] s, r < 1 := by
    have upper : ∀ᶠ r in 𝓝 s, r < 1 := Iio_mem_nhds before
    exact upper.filter_mono nhdsWithin_le_nhds
  obtain ⟨r, close, greater, less⟩ :=
    ((near.filter_mono nhdsWithin_le_nhds).and (after.and below)).exists
  refine ⟨AffineMap.lineMap a b r, lineMap_mem_segment ℝ a b
    ⟨bounds.1.trans greater.le, less.le⟩, close, ?_⟩
  exact at_p ▸ strict bounds.1 greater

end Unfoldings

namespace Unfoldings.RadialClipTail

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {S : Set E} {q p x : E} (T : RadialClipTail S q p)

theorem radial_outward : 0 ≤ inner ℝ (p - q) (T.tip - p) := by
  have first := congrArg (fun z : E => z - q) T.seed_eq
  simp only [add_sub_cancel_left] at first
  have last : T.tip - p = (1 - T.start) • (T.tip - q) := by
    calc
      T.tip - p = T.tip - (q + T.start • (T.tip - q)) :=
        congrArg (fun z : E => T.tip - z) T.seed_eq
      _ = _ := by module
  rw [first, last, real_inner_smul_left, real_inner_smul_right]
  exact mul_nonneg T.start_pos.le
    (mul_nonneg (sub_nonneg.mpr T.start_le) real_inner_self_nonneg)

theorem local_growth_of_not_tip (member : x ∈ T.carrier) (not_tip : x ≠ T.tip) :
    LocalRadialGrowth T.carrier q x := by
  have different : p ≠ T.tip := by
    intro same
    have singleton : T.carrier = {T.tip} :=
      (congrArg (fun z : E => segment ℝ z T.tip) same).trans (segment_same ℝ _)
    exact not_tip (Set.mem_singleton_iff.mp (singleton.subset member))
  exact localRadialGrowth_of_segment_strict
    (fun nonnegative ordered => dist_lineMap_lt_of_inner_nonneg _ _ _ T.radial_outward
      different nonnegative ordered) member not_tip

end Unfoldings.RadialClipTail
