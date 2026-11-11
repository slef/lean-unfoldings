module

public import Unfoldings.Geometry.RadialSegment
public import Unfoldings.Topology.FiniteClosedActive
public import Mathlib.Topology.Order.Basic

/-! Local radial minima in a finite closed network cannot receive a genuine outward segment. -/

@[expose] public section

namespace Unfoldings

open Filter Topology

theorem finite_closed_cover_locally_lower_bound {E ι : Type*} [TopologicalSpace E] [Finite ι]
    (piece : ι → Set E) (closed : ∀ i, IsClosed (piece i)) (value : E → ℝ) (x : E)
    (bound : ∀ i, x ∈ piece i → ∀ y ∈ piece i, value x ≤ value y) :
    ∀ᶠ y in 𝓝 x, y ∈ ⋃ i, piece i → value x ≤ value y := by
  have active := finite_closed_cover_eventually_active piece closed id continuous_id x
  filter_upwards [active] with y nearby member
  obtain ⟨i, inside⟩ := Set.mem_iUnion.mp member
  exact bound i (nearby i inside) y inside

theorem outward_segment_endpoint_not_local_min {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {S : Set E} {q a b : E}
    (outward : 0 ≤ inner ℝ (a - q) (b - a)) (different : a ≠ b)
    (inside : segment ℝ a b ⊆ S)
    (minimum : ∀ᶠ y in 𝓝 b, y ∈ S → dist q b ≤ dist q y) : False := by
  have tends : Tendsto (fun t : ℝ => AffineMap.lineMap b a t) (𝓝 0) (𝓝 b) := by
    simpa only [ContinuousAt, AffineMap.lineMap_apply_zero] using
      (AffineMap.lineMap_continuous :
        Continuous (fun t : ℝ => AffineMap.lineMap b a t)).continuousAt (x := (0 : ℝ))
  have near : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      AffineMap.lineMap b a t ∈ S → dist q b ≤ dist q (AffineMap.lineMap b a t) :=
    (tends.eventually minimum).filter_mono nhdsWithin_le_nhds
  have small : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (show ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 from Iio_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  have positive : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, after, before, bound⟩ := (positive.and (small.and near)).exists
  have reverse : AffineMap.lineMap b a t = AffineMap.lineMap a b (1 - t) := by
    simp only [AffineMap.lineMap_apply_module']
    module
  have member : AffineMap.lineMap b a t ∈ S := by
    rw [reverse]
    exact inside (lineMap_mem_segment ℝ _ _ ⟨by linarith, by linarith⟩)
  have less := dist_lineMap_lt_of_inner_nonneg q a b outward different
    (t := 1 - t) (s := 1) (by linarith) (by linarith)
  rw [AffineMap.lineMap_apply_one, ← reverse] at less
  exact not_lt_of_ge (bound member) less

end Unfoldings
