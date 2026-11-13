module

public import Unfoldings.Geometry.SpatialEnvelopeTriangles
public import Unfoldings.Geometry.ConstrainedTriangleRefinement

/-! Prescribed line refinements preserve the actual spatial supports and parent triangles. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z : ℝ} (T : Triangulation family Z)

/-- Align a physical roof mesh to a finite collection of proper lines. -/
def alignToLines {J : Type u} [Finite J] (equation : J → Plane →ᵃ[ℝ] ℝ)
    (proper : ∀ j, equation j ≠ 0) (inside : (interior (clip family Z)).Nonempty) :
    ConstrainedTriangulation family equation Z := by
  let := T.finite
  let Small := Set.range equation
  let : Finite Small := (Set.finite_range equation).to_subtype
  let R := constrainedTriangleRefinement T.projectedTriangle (fun j : Small => j.val)
    (fun j => by obtain ⟨k, equal⟩ := j.property; exact equal ▸ proper k)
    (T.cover ▸ AffineEnvelope.convex_clip (fun i => (family i).height) Z)
    (T.cover ▸ inside)
  let P : ConstrainedTriangulation family equation Z :=
    { Index := R.Index
      finite := R.finite
      projectedTriangle := R.triangle
      support i := T.support (R.parent i)
      cover := T.cover.trans R.cover
      separated := R.separated
      active i p member := T.active (R.parent i) p (R.subset_parent i member)
      signs i j := R.signs i ⟨equation j, j, rfl⟩
      constrained i p member j := R.constrained i p member ⟨equation j, j, rfl⟩ }
  exact P.refined

theorem alignToLines_conforming {J : Type u} [Finite J]
    (equation : J → Plane →ᵃ[ℝ] ℝ) (proper : ∀ j, equation j ≠ 0)
    (inside : (interior (clip family Z)).Nonempty) :
    TriangleFamily.Conforming (T.alignToLines equation proper inside).projectedTriangle := by
  let := T.finite
  exact Triangulation.refined_conforming _

/-- Line meshing records an actual old triangle parent and preserves its support label. -/
theorem alignToLines_subordinate {J : Type u} [Finite J]
    (equation : J → Plane →ᵃ[ℝ] ℝ) (proper : ∀ j, equation j ≠ 0)
    (inside : (interior (clip family Z)).Nonempty) :
    let L := T.alignToLines equation proper inside
    ∃ parent : L.Index → T.Index, ∀ i,
      (L.projectedTriangle i).carrier ⊆ (T.projectedTriangle (parent i)).carrier ∧
        L.support i = T.support (parent i) := by
  let := T.finite
  let Small := Set.range equation
  let : Finite Small := (Set.finite_range equation).to_subtype
  let R := constrainedTriangleRefinement T.projectedTriangle (fun j : Small => j.val)
    (fun j => by obtain ⟨k, equal⟩ := j.property; exact equal ▸ proper k)
    (T.cover ▸ AffineEnvelope.convex_clip (fun i => (family i).height) Z)
    (T.cover ▸ inside)
  let := R.finite
  let G := commonTriangleRefinement R.triangle
  exact ⟨fun i => R.parent i.1, fun i =>
    ⟨(G.triangle_subset i).trans (R.subset_parent i.1), rfl⟩⟩

end Unfoldings.SpatialEnvelope.Triangulation
