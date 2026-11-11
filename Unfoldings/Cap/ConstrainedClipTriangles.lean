module

public import Unfoldings.Cap.ClipRealization
public import Unfoldings.Geometry.ConstrainedTriangleRefinement
public import Unfoldings.Geometry.WholeEdgeSubdivision

/-! Conforming physical roof triangulations that preserve all original cap edges exactly. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

structure LineAlignedClip (Z : ℝ) {J : Type} (equation : J → Plane →ᵃ[ℝ] ℝ) where
  partition : K.ClipSpatialTriangles Z
  conforming : TriangleFamily.Conforming partition.projectedTriangle
  signs : partition.Index → J → Bool
  side : ∀ i p, p ∈ (partition.projectedTriangle i).carrier → ∀ j,
    0 ≤ AffineArrangement.signed (equation j) (signs i j) p

namespace ClipSpatialTriangles

variable {K} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

/-- Insert prescribed supporting lines and then make the resulting physical partition conforming. -/
def alignToLines {J : Type} [Finite J] (equation : J → Plane →ᵃ[ℝ] ℝ)
    (proper : ∀ j, equation j ≠ 0) (lower : Z < 0) : K.LineAlignedClip Z equation := by
  let := T.finite
  let R := constrainedTriangleRefinement T.projectedTriangle equation proper
    (T.cover ▸ K.convex_clipFootprint Z) (T.cover ▸ K.clip_interior_nonempty lower)
  let P : K.ClipSpatialTriangles Z :=
    { Index := R.Index
      finite := R.finite
      projectedTriangle := R.triangle
      face i := T.face (R.parent i)
      cover := T.cover.trans R.cover
      separated := R.separated
      active i p member := T.active (R.parent i) p (R.subset_parent i member) }
  exact
    { partition := P.refined
      conforming := P.refined_conforming
      signs i j := R.signs i.1 j
      side i p member j := R.constrained i.1 p (P.commonRefinement.triangle_subset i member) j }

end ClipSpatialTriangles

/-- The supporting coordinates of all original input faces, indexed by a small finite type. -/
def originalEdgeEquations : Fin (Fintype.card Face) × Fin 3 → Plane →ᵃ[ℝ] ℝ :=
  fun i => (K.projectedTriangle ((Fintype.equivFin Face).symm i.1)).coord i.2

theorem originalEdgeEquations_ne_zero (i : Fin (Fintype.card Face) × Fin 3) :
    K.originalEdgeEquations i ≠ 0 :=
  (K.projectedTriangle ((Fintype.equivFin Face).symm i.1)).coord_ne_zero i.2

namespace ClipSpatialTriangles

variable {K} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

/-- A constructed conforming roof clip respecting all original input edge supporting lines. -/
def preserveOriginalEdges (lower : Z < 0) : K.LineAlignedClip Z K.originalEdgeEquations :=
  T.alignToLines K.originalEdgeEquations K.originalEdgeEquations_ne_zero lower

end ClipSpatialTriangles

namespace LineAlignedClip

variable {K} {Z : ℝ} (L : K.LineAlignedClip Z K.originalEdgeEquations)

/-- Every original edge and selected cut is exactly a union of whole new edges. -/
theorem original_edge_eq_union_subedges (lower : Z < 0) (f : Face) (e : Fin 3) :
    (K.projectedTriangle f).edge e =
      ⋃ a : {a : L.partition.Index × Fin 3 //
          (L.partition.projectedTriangle a.1).edge a.2 ⊆ (K.projectedTriangle f).edge e},
        (L.partition.projectedTriangle a.val.1).edge a.val.2 := by
  let := L.partition.finite
  have cover : (K.projectedTriangle f).edge e ⊆
      ⋃ i, (L.partition.projectedTriangle i).carrier := by
    intro p member
    exact L.partition.cover.subset
      ((K.projectedTriangle_subset_clippedSupportCell lower.le f
        ((K.projectedTriangle f).edge_subset e member)).1)
  refine TriangleFamily.edge_eq_union_subedges L.partition.projectedTriangle
    (K.projectedTriangle f) e cover (fun i k => L.signs i ((Fintype.equivFin Face) f, k)) ?_
  intro i k p member
  simpa only [originalEdgeEquations, Equiv.symm_apply_apply] using
    L.side i p member ((Fintype.equivFin Face) f, k)

end LineAlignedClip
end Unfoldings.ConvexCap
