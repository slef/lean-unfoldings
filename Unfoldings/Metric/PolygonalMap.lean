module

public import Unfoldings.Metric.Polygonal
public import Unfoldings.Geometry.ConvexLocalBounds

/-!
# Locally nonexpanding maps descend to polygonal metrics

A center bound in the ambient subspace topology propagates along every
allowed straight segment and then along finite routes. This connects local
metric charts with the actual intrinsic distance, without a global convexity
assumption on the whole region.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal NNReal

namespace Unfoldings.PolygonalPoint

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y]
  {s : Set E}

theorem lipschitz_of_local_center_bounds (f : s → Y)
    (local_bound : ∀ x : s, ∀ᶠ y in 𝓝 x, dist (f y) (f x) ≤ dist y x) :
    LipschitzWith 1 (f ∘ toSubtype) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul]
  change edist (f (toSubtype x)) (f (toSubtype y)) ≤ Route.distance (stepCost (s := s)) x y
  apply Route.le_distance (stepCost (s := s))
    (fun a b => edist (f (toSubtype a)) (f (toSubtype b)))
    (fun _ => edist_self _) (fun _ _ _ => edist_triangle _ _ _)
  intro a b
  by_cases inside : segment ℝ a.val b.val ⊆ s
  · let g : segment ℝ a.val b.val → s := fun z => ⟨z.val, inside z.property⟩
    have continuous_g : Continuous g := continuous_subtype_val.subtype_mk _
    have local_segment (z : segment ℝ a.val b.val) :
        ∀ᶠ w in 𝓝 z, dist (f (g w)) (f (g z)) ≤ (1 : ℝ≥0) * dist w z := by
      filter_upwards [continuous_g.continuousAt.tendsto.eventually (local_bound (g z))]
        with w hw
      simpa only [g, Subtype.dist_eq, NNReal.coe_one, one_mul] using hw
    have bound := convex_subtype_lipschitzWith_of_center_bounds _ (convex_segment _ _)
      (f ∘ g) 1 local_segment
    have endpoint := bound ⟨a.val, left_mem_segment ℝ _ _⟩ ⟨b.val, right_mem_segment ℝ _ _⟩
    simpa only [stepCost, ite_eq_left inside, ENNReal.coe_one, one_mul,
      Function.comp_def, g, toSubtype, Subtype.edist_eq] using endpoint
  · simp only [stepCost, ite_eq_right inside, le_top]

end Unfoldings.PolygonalPoint
