module

public import Unfoldings.Geometry.ConvexCover

/-! Center bounds on a convex subtype imply a global Lipschitz bound. -/

@[expose] public section

open Set Filter Topology
open scoped NNReal

namespace Unfoldings

theorem convex_subtype_lipschitzWith_of_center_bounds {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y]
    (s : Set E) (convex_s : Convex ℝ s) (f : s → Y) (K : ℝ≥0)
    (local_bound : ∀ x : s, ∀ᶠ y in 𝓝 x, dist (f y) (f x) ≤ K * dist y x) :
    LipschitzWith K f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let extension : E → Y := Function.extend Subtype.val f (fun _ => f x)
  have agrees (z : s) : extension z.val = f z := Subtype.val_injective.extend_apply _ _ z
  have local_extension (z : E) (hz : z ∈ s) :
      ∀ᶠ w in 𝓝[s] z, dist (extension w) (extension z) ≤ K * dist w z := by
    rw [nhdsWithin_eq_map_subtype_coe hz, Filter.eventually_map]
    have at_z : extension z = f ⟨z, hz⟩ := agrees ⟨z, hz⟩
    filter_upwards [local_bound ⟨z, hz⟩] with w hw
    rw [agrees w, at_z]
    exact hw
  have bound := convex_lipschitzOnWith_of_center_bounds s convex_s extension K local_extension
  change dist (f x) (f y) ≤ (K : ℝ) * dist x.val y.val
  simpa only [agrees] using bound.dist_le_mul x.val x.property y.val y.property

end Unfoldings
