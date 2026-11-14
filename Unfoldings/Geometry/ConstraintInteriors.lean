module

public import Unfoldings.Geometry.AffineMaximum
public import Unfoldings.Geometry.ConstrainedEdgeSubdivision
public import Unfoldings.Geometry.ConstrainedTriangleRefinement
public import Unfoldings.Geometry.SpatialEnvelopeTriangles

/-! Actual line constraints keep complete fine-triangle interiors away from supported curves. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A proper affine weak inequality is strict at every ambient interior point. -/
theorem affine_pos_on_interior_of_nonnegative (height : E →ᵃ[ℝ] ℝ) (proper : height ≠ 0)
    (s : Set E) (side : ∀ x ∈ s, 0 ≤ height x) {x : E} (inside : x ∈ interior s) :
    0 < height x := by
  by_contra not_positive
  have zero : height x = 0 :=
    le_antisymm (le_of_not_gt not_positive) (side x (interior_subset inside))
  have maximum : IsLocalMax (-height) x := by
    apply Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp inside)
    intro y hy
    change -height y ≤ -height x
    rw [zero, neg_zero]
    exact neg_nonpos.mpr (side y hy)
  apply proper
  ext y
  have equality := affine_eq_at_of_localMax (-height) x maximum y
  change -height y = -height x at equality
  rw [zero, neg_zero] at equality
  exact neg_eq_zero.mp equality

namespace TriangleFamily

variable {A B : Type*} (triangles : A → Triangle) (equations : B → Plane →ᵃ[ℝ] ℝ)

theorem interior_avoids_supported_curve (proper : ∀ j, equations j ≠ 0)
    (signs : A → B → Bool)
    (side : ∀ i p, p ∈ (triangles i).carrier → ∀ j,
      0 ≤ AffineArrangement.signed (equations j) (signs i j) p)
    {curve : Set Plane} (support : ∀ p ∈ curve, ∃ j, equations j p = 0) (i : A) :
    Disjoint (interior (triangles i).carrier) curve := by
  apply Set.disjoint_left.mpr
  intro p inside on_curve
  obtain ⟨j, zero⟩ := support p on_curve
  have positive := affine_pos_on_interior_of_nonnegative
    (AffineArrangement.signed (equations j) (signs i j))
    (AffineArrangement.signed_ne_zero _ (proper j) _) (triangles i).carrier
    (fun x hx => side i x hx j) inside
  rw [(AffineArrangement.signed_eq_zero_iff _ _ _).mpr zero] at positive
  exact lt_irrefl 0 positive

end TriangleFamily

namespace ConstrainedTriangleRefinement

variable {I J : Type}
  {original : I → Triangle} {extra : J → Plane →ᵃ[ℝ] ℝ}
  (T : ConstrainedTriangleRefinement original extra)

theorem interior_avoids_supported_curve (proper : ∀ j, extra j ≠ 0)
    {curve : Set Plane} (support : ∀ p ∈ curve, ∃ j, extra j p = 0) (i : T.Index) :
    Disjoint (interior (T.triangle i).carrier) curve :=
  TriangleFamily.interior_avoids_supported_curve T.triangle extra proper
    T.signs T.constrained support i

end ConstrainedTriangleRefinement

namespace SpatialEnvelope.ConstrainedTriangulation

universe u

variable {I J : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {equations : J → Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  (T : ConstrainedTriangulation family equations Z)

theorem interior_avoids_supported_curve (proper : ∀ j, equations j ≠ 0)
    {curve : Set Plane} (support : ∀ p ∈ curve, ∃ j, equations j p = 0) (i : T.Index) :
    Disjoint (interior (T.projectedTriangle i).carrier) curve :=
  TriangleFamily.interior_avoids_supported_curve T.projectedTriangle equations proper
    T.signs T.constrained support i

end SpatialEnvelope.ConstrainedTriangulation
end Unfoldings
