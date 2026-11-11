module

public import Unfoldings.Cap.SkirtCurvatureSeeds
public import Unfoldings.Cap.ParentSegments
public import Unfoldings.Cap.Boundary

/-!
# Curvature coverage by the constructed geometric extended cuts

Keep the selected original parent edges and append the meshed radial skirt
components. Every positive-curvature vertex of the resulting actual roof clip
lies on that geometric cut set. Its graph-theoretic forest property and cut
realization remain separate obligations.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)

variable {Z : ℝ}

/-- The actual whole projected edges selected by the original source-centered forest. -/
def projectedCutCarrier : Set Plane :=
  ⋃ e : {v : C.Vertex Set.univ // v ∉ M.parents.roots},
    segment ℝ (K.projectedVertex e.val) (K.projectedVertex (M.parents.parent e.val))

theorem projectedVertex_mem_cutCarrier (v : C.Vertex Set.univ) (nonroot : v ∉ M.parents.roots) :
    K.projectedVertex v ∈ M.projectedCutCarrier :=
  Set.mem_iUnion.mpr ⟨⟨v, nonroot⟩, left_mem_segment ℝ _ _⟩

/-- Actual original cuts and selected skirt continuations cover all refined positive curvature. -/
theorem extended_cut_curvature_covered (T : K.ClipSpatialTriangles Z)
    (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (positive : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside positive lower
    let L := F.mesh T lower
    let Q := L.partition.normalizedCap L.conforming lower
    letI := @Fintype.ofFinite _ L.partition.finite
    ∀ v : L.partition.pairedComplex.Vertex Set.univ,
      0 < L.partition.pairedComplex.interiorAngularDefect Set.univ v →
        Q.projectedVertex v ∈ M.projectedCutCarrier ∪
          ⋃ c : F.Component, (F.componentTail c).carrier := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside positive lower
  let L := F.mesh T lower
  let Q := L.partition.normalizedCap L.conforming lower
  let := @Fintype.ofFinite _ L.partition.finite
  refine fun v curved => ?_
  rcases T.cornerMesh_curvature_covered inside positive lower conforming height v curved with
    original | tail
  · obtain ⟨w, at_point⟩ := original
    by_cases boundary : C.IsBoundaryVertex Set.univ w
    · obtain ⟨⟨f, k⟩, at_corner⟩ := C.vertexOfCorner_surjective Set.univ w
      have corner : (K.projectedTriangle f).vertex k = Q.projectedVertex v :=
        (K.projectedVertex_ofCorner f k).symm.trans
          ((congrArg K.projectedVertex at_corner).trans at_point)
      have rim : (K.projectedTriangle f).vertex k ∉ interior K.footprint := by
        intro member
        have corner_w : (K.projectedTriangle f).vertex k = K.projectedVertex w :=
          (K.projectedVertex_ofCorner f k).symm.trans (congrArg K.projectedVertex at_corner)
        have at_w : K.projectedVertex w ∈ interior K.footprint :=
          corner_w ▸ member
        exact ((K.projectedVertex_mem_interior_iff w).mp at_w) boundary
      exact Or.inr (corner ▸ T.cornerTails_original_rim_corner inside positive lower f k rim)
    · have nonroot : w ∉ M.parents.roots := by rw [M.roots_eq]; exact boundary
      exact Or.inl (at_point ▸ M.projectedVertex_mem_cutCarrier w nonroot)
  · exact Or.inr tail

end Unfoldings.ConvexCap.SectorForest
