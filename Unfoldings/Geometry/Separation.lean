module

public import Unfoldings.Geometry.Triangle
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Nonoverlap certificates with boundary contact allowed

The finite-vertex separator interface is inspired by the `Separation` and
`VertexCertificate` modules of slef/EdgeUnfoldings, snapshot
56caca8cdc44dbc2f839e93808088d56ea3f0780. Here it is independent of embedded
convex polyhedra and of any chosen cut tree.
-/

@[expose] public section

namespace Unfoldings

/-- A nonconstant linear separator proves disjoint interiors, allowing equality on boundaries. -/
theorem disjoint_interiors_of_separator {A B : Set Plane} (height : Plane →L[ℝ] ℝ)
    (surjective : Function.Surjective height) (level : ℝ)
    (upper : ∀ x ∈ A, height x ≤ level) (lower : ∀ x ∈ B, level ≤ height x) :
    Disjoint (interior A) (interior B) := by
  have strict : interior A ⊆ height ⁻¹' Set.Iio level := by
    have included : A ⊆ height ⁻¹' Set.Iic level := upper
    have bound := interior_mono included
    rwa [height.interior_preimage surjective, interior_Iic] at bound
  exact Set.disjoint_left.mpr fun x hx hy =>
    (not_lt_of_ge (lower x (interior_subset hy))) (strict hx)

namespace Triangle

/-- A linear upper bound on the placed corners holds on the whole placed triangle. -/
theorem image_le_of_vertices (T : Triangle) (place : Plane →ᵃ[ℝ] Plane)
    (height : Plane →L[ℝ] ℝ) (level : ℝ)
    (corners : ∀ i, height (place (T.vertex i)) ≤ level) :
    ∀ x ∈ place '' T.carrier, height x ≤ level := by
  have convex : Convex ℝ {x : Plane | height (place x) ≤ level} :=
    ((convex_Iic level).linear_preimage height.toLinearMap).affine_preimage place
  have inclusion : T.carrier ⊆ {x : Plane | height (place x) ≤ level} :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact corners i) convex
  rintro _ ⟨x, hx, rfl⟩
  exact inclusion hx

/-- The corresponding lower bound also needs only the original corners. -/
theorem image_ge_of_vertices (T : Triangle) (place : Plane →ᵃ[ℝ] Plane)
    (height : Plane →L[ℝ] ℝ) (level : ℝ)
    (corners : ∀ i, level ≤ height (place (T.vertex i))) :
    ∀ x ∈ place '' T.carrier, level ≤ height x := by
  have convex : Convex ℝ {x : Plane | level ≤ height (place x)} :=
    ((convex_Ici level).linear_preimage height.toLinearMap).affine_preimage place
  have inclusion : T.carrier ⊆ {x : Plane | level ≤ height (place x)} :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact corners i) convex
  rintro _ ⟨x, hx, rfl⟩
  exact inclusion hx

theorem disjoint_interiors_of_vertex_separator (T U : Triangle)
    (left right : Plane →ᵃ[ℝ] Plane) (height : Plane →L[ℝ] ℝ)
    (surjective : Function.Surjective height) (level : ℝ)
    (upper : ∀ i, height (left (T.vertex i)) ≤ level)
    (lower : ∀ i, level ≤ height (right (U.vertex i))) :
    Disjoint (interior (left '' T.carrier)) (interior (right '' U.carrier)) :=
  disjoint_interiors_of_separator height surjective level
    (T.image_le_of_vertices left height level upper)
    (U.image_ge_of_vertices right height level lower)

end Triangle
end Unfoldings
