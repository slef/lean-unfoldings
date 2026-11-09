module

public import Unfoldings.Path.Distance
public import Unfoldings.Path.Reparameterization
public import Unfoldings.Geometry.ConvexLocalBounds

/-!
# Local nonexpansion controls intrinsic path distance

Rectifiable paths first receive bounded-speed parametrizations. Center bounds
then propagate along the parameter interval, so their mapped paths keep that
speed bound. This proves nonexpansion for intrinsic path distance even when
the map has no global bound for the original ambient distances.
-/

@[expose] public section

open Filter Topology
open scoped NNReal ENNReal

namespace Path

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem lipschitz_map_of_local_center_bounds {a b : X} (q : Path a b) {K : ℝ≥0}
    (speed : LipschitzWith K q) (f : X → Y)
    (local_bound : ∀ x, ∀ᶠ y in 𝓝 x, dist (f y) (f x) ≤ dist y x) :
    LipschitzWith K (f ∘ q) := by
  apply Unfoldings.convex_subtype_lipschitzWith_of_center_bounds
    (Set.Icc (0 : ℝ) 1) (convex_Icc _ _)
  intro t
  filter_upwards [q.continuous.continuousAt.tendsto.eventually (local_bound (q t))] with u hu
  exact hu.trans (speed.dist_le_mul u t)

theorem eDistance_map_le_of_local_center_bounds (f : X → Y) (continuous : Continuous f)
    (local_bound : ∀ x, ∀ᶠ y in 𝓝 x, dist (f y) (f x) ≤ dist y x) (a b : X) :
    eDistance (f a) (f b) ≤ eDistance a b := by
  apply le_iInf
  intro p
  by_cases infinite : p.eLength = ⊤
  · rw [infinite]
    exact le_top
  · obtain ⟨q, speed, _range, _length⟩ := p.exists_lipschitz_reparameterization infinite
    have mapped_speed := q.lipschitz_map_of_local_center_bounds speed f local_bound
    exact (q.map continuous).eDistance_le_eLength.trans
      (((q.map continuous).eLength_le_of_lipschitz mapped_speed).trans_eq
        (ENNReal.coe_toNNReal infinite))

theorem eDistance_eq_of_homeomorph_local_center_bounds (H : X ≃ₜ Y)
    (forward : ∀ x, ∀ᶠ y in 𝓝 x, dist (H y) (H x) ≤ dist y x)
    (inverse : ∀ x, ∀ᶠ y in 𝓝 x, dist (H.symm y) (H.symm x) ≤ dist y x) (a b : X) :
    eDistance (H a) (H b) = eDistance a b := by
  apply le_antisymm (eDistance_map_le_of_local_center_bounds H H.continuous forward a b)
  simpa only [H.symm_apply_apply] using
    eDistance_map_le_of_local_center_bounds H.symm H.symm.continuous inverse (H a) (H b)

end Path
