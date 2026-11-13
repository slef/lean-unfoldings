module

public import Unfoldings.Roof.CompletionOriginalRetention
public import Unfoldings.Roof.OriginalCutCarrier
public import Unfoldings.Roof.CompletionExtendedMesh
public import Unfoldings.Geometry.SharedEdgeCutSet

/-! Exterior radial cuts preserve exactly the retained original seam classes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (L : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionCutRestrictionIndexFintype : Fintype L.partition.Index :=
  @Fintype.ofFinite _ L.partition.finite

open Classical in
theorem originalRetain_union_skirt_eq (retain : Set C.Seam) (skirt : Set Plane)
    (outside : ∀ p ∈ skirt, p ∉ interior K.footprint) :
    L.partition.pairedComplex.restrictRetain L.originalPieceSet
        (L.partition.retainOutside (K.projectedCutSet retain ∪ skirt)) =
      L.originalRetain retain := by
  have original_member (i : L.originalPieceSet) :
      (L.partition.projectedTriangle i.val).carrier ⊆ K.footprint := by
    intro p member
    rw [K.footprint_eq_union_projectedTriangles]
    exact Set.mem_iUnion.mpr ⟨L.originalParent i, L.originalParent_contains i member⟩
  ext s
  change (¬ _ ⊆ K.projectedCutSet retain ∪ skirt) ↔ (¬ _ ⊆ K.projectedCutSet retain)
  constructor
  · intro kept selected
    exact kept (selected.trans Set.subset_union_left)
  · intro kept selected
    apply kept
    apply Triangle.shared_edge_subset_cutset_of_skirt
        (L.partition.projectedTriangle (L.originalComplex.left s).face.val)
        (L.partition.projectedTriangle (L.originalComplex.right s).face.val) _ _
        (L.partition.paired_seam_projected_edge s.val)
        (L.partition.separated
          (TriangleFamily.seamPair L.partition.projectedTriangle s.val).different_faces)
        (original_member _) (original_member _) (K.isClosed_projectedCutSet retain)
        outside selected


end Unfoldings.ConvexRoof.CompletionMesh

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {φ : ℝ} {region : Set Plane} {J : Type u} {extra : J → Plane →ᵃ[ℝ] ℝ}
  (E : K.CompletionMesh φ region extra)

theorem extendedRetain_restrict_original_eq :
    let L := E.radialMesh M.inside
    letI := @Fintype.ofFinite _ L.mesh.finite
    L.mesh.toTriangulation.pairedComplex.restrictRetain L.originalPart.originalPieceSet
      (M.extendedRetain E) = L.originalPart.originalRetain M.retain := by
  let F := E.cornerTails M.inside
  let L := E.radialMesh M.inside
  let := @Fintype.ofFinite _ L.mesh.finite
  change L.mesh.toTriangulation.pairedComplex.restrictRetain L.originalPart.originalPieceSet
    (L.mesh.toTriangulation.retainOutside (M.projectedCutCarrier ∪
      ⋃ c : F.Component, (F.componentTail c).carrier)) = _
  rw [M.projectedCutCarrier_eq_projectedCutSet]
  apply L.originalPart.originalRetain_union_skirt_eq
  intro p member
  obtain ⟨c, member⟩ := Set.mem_iUnion.mp member
  exact F.component_outside c member

end Unfoldings.ConvexRoof.SectorForest
