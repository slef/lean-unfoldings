module

public import Unfoldings.Cap.ClipOriginalRetention
public import Unfoldings.Cap.OriginalCutCarrier
public import Unfoldings.Cap.ExtendedCutMesh
public import Unfoldings.Geometry.SharedEdgeCutSet

/-! Actual exterior skirt cuts leave precisely the original retained seams on original faces. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexCap C}

namespace LineAlignedClip

variable {Z : ℝ} (L : K.LineAlignedClip Z K.originalEdgeEquations)

local instance cutRestrictionIndexFintype : Fintype L.partition.Index :=
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

end LineAlignedClip

namespace SectorForest

variable {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} {q : Plane}

open Classical in
theorem extendedRetain_restrict_original_eq (T : K.ClipSpatialTriangles Z)
    (F : K.SkirtTailFamily Z q) (lower : Z < 0) :
    let L := F.mesh T lower
    letI := @Fintype.ofFinite _ L.partition.finite
    L.partition.pairedComplex.restrictRetain L.originalPart.originalPieceSet
        (M.extendedRetain T F lower) = L.originalPart.originalRetain M.retain := by
  let L := F.mesh T lower
  let := @Fintype.ofFinite _ L.partition.finite
  change L.partition.pairedComplex.restrictRetain L.originalPart.originalPieceSet
      (L.partition.retainOutside (M.projectedCutCarrier ∪
        ⋃ c : F.Component, (F.componentTail c).carrier)) = _
  rw [M.projectedCutCarrier_eq_projectedCutSet]
  apply L.originalPart.originalRetain_union_skirt_eq
  intro p member
  obtain ⟨c, member⟩ := Set.mem_iUnion.mp member
  exact F.component_outside c member

end SectorForest
end Unfoldings.ConvexCap
