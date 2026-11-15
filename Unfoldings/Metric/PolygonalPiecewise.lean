module

public import Unfoldings.Metric.Polygonal
public import Unfoldings.Metric.ConvexCover

/-! Piecewise nonexpansion determines maps on the actual intrinsic polygonal metric. -/

@[expose] public section

open scoped ENNReal NNReal

namespace Unfoldings.PolygonalPoint

variable {E Y I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [EMetricSpace Y] [Finite I] {s : Set E}

/-- Closed pieces need not be convex: each allowed straight step is controlled
by its own finite closed-piece cover. The target may have infinite distances. -/
theorem lipschitz_of_finite_closed_cover (cells : I → Set E)
    (closed : ∀ i, IsClosed (cells i)) (cover : s ⊆ ⋃ i, cells i)
    (f : s → Y)
    (bounded : ∀ i, LipschitzOnWith 1 f {x | x.val ∈ cells i}) :
    LipschitzWith 1 (f ∘ toSubtype) := by
  intro x y
  simp only [ENNReal.coe_one, one_mul]
  change edist (f (toSubtype x)) (f (toSubtype y)) ≤
    Route.distance (stepCost (s := s)) x y
  apply Route.le_distance (stepCost (s := s))
    (fun a b => edist (f (toSubtype a)) (f (toSubtype b)))
    (fun _ => edist_self _) (fun _ _ _ => edist_triangle _ _ _)
  intro a b
  by_cases inside : segment ℝ a.val b.val ⊆ s
  · let line := segment ℝ a.val b.val
    let g : line → s := fun z => ⟨z.val, inside z.property⟩
    let pieces (i : I) : Set line := {z | z.val ∈ cells i}
    have pieces_closed (i : I) : IsClosed (pieces i) :=
      (closed i).preimage continuous_subtype_val
    have pieces_cover : (⋃ i, pieces i) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (cover (inside z.property))
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    have bound : LipschitzWith 1 (f ∘ g) := by
      apply convex_subtype_emetric_lipschitzWith_of_finite_closed_cover
        line (convex_segment _ _) pieces pieces_closed pieces_cover
      intro i p hp q hq
      exact bounded i hp hq
    have endpoints := bound ⟨a.val, left_mem_segment ℝ _ _⟩
      ⟨b.val, right_mem_segment ℝ _ _⟩
    simpa only [stepCost, ite_eq_left inside, Function.comp_def, g, toSubtype,
      Subtype.edist_eq, ENNReal.coe_one, one_mul] using endpoints
  · simp only [stepCost, ite_eq_right inside]
    exact le_top

end Unfoldings.PolygonalPoint
