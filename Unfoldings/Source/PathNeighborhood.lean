module

public import Unfoldings.Source.CompactPaths
public import Mathlib.Topology.MetricSpace.Thickening

/-! Whole compact parameter intervals stay in an open chart under small path perturbations. -/

@[expose] public section

open scoped Topology BoundedContinuousFunction

namespace Unfoldings.SourcePath

variable {X : Type*} [MetricSpace X] {source : X}

theorem eventually_inside_on_compact (p : SourcePath source) {K : Set unitInterval}
    (compact : IsCompact K) {D : Set X} (open_D : IsOpen D)
    (inside : ∀ t ∈ K, p.path t ∈ D) :
    ∀ᶠ q in 𝓝 p, ∀ t ∈ K, q.path t ∈ D := by
  have image_inside : p.path '' K ⊆ D := by
    rintro _ ⟨t, ht, rfl⟩
    exact inside t ht
  obtain ⟨δ, positive, clear⟩ := (compact.image p.path.continuous).exists_thickening_subset_open
    open_D image_inside
  filter_upwards [Metric.ball_mem_nhds p positive] with q near
  intro t ht
  have bound := BoundedContinuousFunction.dist_coe_le_dist
    (f := q.toBounded) (g := p.toBounded) t
  change dist (q.path t) (p.path t) ≤ dist q p at bound
  exact clear (Metric.mem_thickening_iff.mpr
    ⟨p.path t, ⟨t, ht, rfl⟩, bound.trans_lt near⟩)

theorem isOpen_paths_inside_on_compact {K : Set unitInterval} (compact : IsCompact K)
    {D : Set X} (open_D : IsOpen D) :
    IsOpen {p : SourcePath source | ∀ t ∈ K, p.path t ∈ D} :=
  isOpen_iff_mem_nhds.mpr (fun p inside => p.eventually_inside_on_compact compact open_D inside)

end Unfoldings.SourcePath
