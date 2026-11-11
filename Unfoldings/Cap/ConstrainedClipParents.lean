module

public import Unfoldings.Cap.ConstrainedClipTriangles

/-! Line-aligned roof triangles retain actual parents in the preceding physical partition. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.ClipSpatialTriangles

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

theorem alignToLines_subordinate {J : Type} [Finite J] (equation : J → Plane →ᵃ[ℝ] ℝ)
    (proper : ∀ j, equation j ≠ 0) (lower : Z < 0) :
    let L := T.alignToLines equation proper lower
    ∃ parent : L.partition.Index → T.Index, ∀ i,
      (L.partition.projectedTriangle i).carrier ⊆ (T.projectedTriangle (parent i)).carrier ∧
        L.partition.face i = T.face (parent i) := by
  let := T.finite
  let R := constrainedTriangleRefinement T.projectedTriangle equation proper
    (T.cover ▸ K.convex_clipFootprint Z) (T.cover ▸ K.clip_interior_nonempty lower)
  let := R.finite
  let G := commonTriangleRefinement R.triangle
  exact ⟨fun i => R.parent i.1, fun i =>
    ⟨(G.triangle_subset i).trans (R.subset_parent i.1), rfl⟩⟩

end Unfoldings.ConvexCap.ClipSpatialTriangles
