module

public import Unfoldings.Metric.ConvexCover

/-! Local common distance bounds extend across convex domains, including extended-metric targets. -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped NNReal

namespace Unfoldings

/-- A common local Lipschitz bound on an actual convex subtype is global.
The target may have infinite distances between its other components. -/
theorem convex_subtype_emetric_lipschitzWith_of_local {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [EMetricSpace Y]
    (s : Set E) (convex_s : Convex ℝ s) (f : s → Y) (K : ℝ≥0)
    (local_bound : ∀ x : s, ∃ r : ℝ, 0 < r ∧ LipschitzOnWith K f (Metric.ball x r)) :
    LipschitzWith K f := by
  have continuous_f : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨r, positive, bounded⟩ := local_bound x
    exact bounded.continuousOn.continuousAt (Metric.ball_mem_nhds x positive)
  intro x y
  let : ContractibleSpace s := convex_s.contractibleSpace ⟨x.val, x.property⟩
  let g : s → Set.range f := fun z => ⟨f z, z, rfl⟩
  have continuous_g : Continuous g := continuous_f.subtype_mk (fun z => ⟨z, rfl⟩)
  have surjective_g : Function.Surjective g := by
    rintro ⟨z, w, rfl⟩
    exact ⟨w, rfl⟩
  let : ConnectedSpace (Set.range f) := surjective_g.connectedSpace continuous_g
  let : MetricSpace (Set.range f) := EMetricSpace.toMetricSpace
    (fun a b => edist_ne_top_of_preconnected a b)
  let extension : E → Set.range f := Function.extend Subtype.val g (fun _ => g x)
  have agrees (z : s) : extension z.val = g z := Subtype.val_injective.extend_apply _ _ z
  have center_bound (z : s) : ∀ᶠ w in 𝓝 z, dist (g w) (g z) ≤ K * dist w z := by
    obtain ⟨r, positive, bounded⟩ := local_bound z
    have bounded_g : LipschitzOnWith K g (Metric.ball z r) := bounded
    filter_upwards [Metric.ball_mem_nhds z positive] with w hw
    exact bounded_g.dist_le_mul w hw z (Metric.mem_ball_self positive)
  have local_extension (z : E) (hz : z ∈ s) :
      ∀ᶠ w in 𝓝[s] z, dist (extension w) (extension z) ≤ K * dist w z := by
    rw [nhdsWithin_eq_map_subtype_coe hz, Filter.eventually_map]
    have at_z : extension z = g ⟨z, hz⟩ := agrees ⟨z, hz⟩
    filter_upwards [center_bound ⟨z, hz⟩] with w hw
    rw [agrees w, at_z]
    exact hw
  have bound := convex_lipschitzOnWith_of_center_bounds s convex_s extension K local_extension
  exact (LipschitzOnWith.of_dist_le_mul (fun a _ b _ => by
    simpa only [agrees, Subtype.dist_eq] using
      bound.dist_le_mul a.val a.property b.val b.property) :
      LipschitzOnWith K g Set.univ) (Set.mem_univ x) (Set.mem_univ y)

end Unfoldings
