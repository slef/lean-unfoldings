module

public import Unfoldings.Metric.CenterBounds
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Finite closed-piece maps on convex domains

A common Lipschitz bound on finitely many closed covering pieces yields that
same bound across the whole convex domain. Individual pieces need not extend
to maps on the entire domain and need not themselves be convex.
-/

@[expose] public section

open Set Filter Topology
open scoped NNReal

namespace Unfoldings

/-- Center bounds extend along segments in a convex domain. -/
theorem convex_lipschitzOnWith_of_center_bounds {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y]
    (s : Set E) (convex_s : Convex ℝ s) (f : E → Y) (K : ℝ≥0)
    (local_bound : ∀ x ∈ s, ∀ᶠ y in 𝓝[s] x, dist (f y) (f x) ≤ K * dist y x) :
    LipschitzOnWith K f s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let line : ℝ → E := AffineMap.lineMap x y
  have inside : MapsTo line (Icc 0 1) s := convex_s.mapsTo_lineMap hx hy
  have continuous_line : Continuous line := (lipschitzWith_lineMap x y).continuous
  have continuous_f := continuousOn_of_center_bounds s f K local_bound
  have along (t : ℝ) (ht : t ∈ Icc 0 1) :
      ∀ᶠ u in 𝓝[Icc 0 1] t,
        dist (f (line u)) (f (line t)) ≤ ((K : ℝ) * dist x y) * dist u t := by
    have near : Tendsto line (𝓝[Icc 0 1] t) (𝓝[s] (line t)) :=
      continuous_line.continuousWithinAt.tendsto_nhdsWithin inside
    filter_upwards [near.eventually (local_bound (line t) (inside ht))] with u hu
    calc
      dist (f (line u)) (f (line t)) ≤ (K : ℝ) * dist (line u) (line t) := hu
      _ = ((K : ℝ) * dist x y) * dist u t := by
        rw [show dist (line u) (line t) = dist u t * dist x y from
          dist_lineMap_lineMap x y u t]
        ring
  have endpoint := interval_distance_of_center_bounds (fun t => f (line t))
    0 1 ((K : ℝ) * dist x y) zero_le_one
    (continuous_f.comp continuous_line.continuousOn inside) along
  simpa only [line, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    sub_zero, mul_one] using endpoint

/-- Finite closed pieces retain their common bound on a convex covering domain. -/
theorem convex_lipschitzOnWith_of_finite_closed_cover {E Y ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y] [Finite ι]
    (s : Set E) (convex_s : Convex ℝ s) (pieces : ι → Set E)
    (closed : ∀ i, IsClosed (pieces i)) (cover : s ⊆ ⋃ i, pieces i)
    (f : E → Y) (K : ℝ≥0) (bounded : ∀ i, LipschitzOnWith K f (pieces i)) :
    LipschitzOnWith K f s :=
  convex_lipschitzOnWith_of_center_bounds s convex_s f K
    (fun x _ => finite_closed_cover_center_bound s pieces closed cover f K bounded x)

/-- The subtype-domain version uses bounds only within the actual covering pieces. -/
theorem convex_subtype_lipschitzWith_of_finite_closed_cover {E Y ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y] [Finite ι]
    (s : Set E) (convex_s : Convex ℝ s) (pieces : ι → Set s)
    (closed : ∀ i, IsClosed (pieces i)) (cover : ⋃ i, pieces i = Set.univ)
    (f : s → Y) (K : ℝ≥0) (bounded : ∀ i, LipschitzOnWith K f (pieces i)) :
    LipschitzWith K f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let extension : E → Y := Function.extend Subtype.val f (fun _ => f x)
  have agrees (z : s) : extension z.val = f z := Subtype.val_injective.extend_apply _ _ z
  have local_subtype (z : s) : ∀ᶠ w in 𝓝 z, dist (f w) (f z) ≤ K * dist w z := by
    have bound := finite_closed_cover_center_bound Set.univ pieces closed
      (by rw [cover]) f K bounded z
    simpa only [nhdsWithin_univ] using bound
  have local_extension (z : E) (hz : z ∈ s) :
      ∀ᶠ w in 𝓝[s] z, dist (extension w) (extension z) ≤ K * dist w z := by
    rw [nhdsWithin_eq_map_subtype_coe hz, Filter.eventually_map]
    have at_z : extension z = f ⟨z, hz⟩ := agrees ⟨z, hz⟩
    filter_upwards [local_subtype ⟨z, hz⟩] with w hw
    rw [agrees w, at_z]
    exact hw
  have bound := convex_lipschitzOnWith_of_center_bounds s convex_s extension K local_extension
  change dist (f x) (f y) ≤ (K : ℝ) * dist x.val y.val
  simpa only [agrees] using bound.dist_le_mul x.val x.property y.val y.property

end Unfoldings
