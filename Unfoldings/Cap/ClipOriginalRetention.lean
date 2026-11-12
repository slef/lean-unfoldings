module

public import Unfoldings.Cap.ClipOriginalSubdivision
public import Unfoldings.Cap.ClipInteriorSeams
public import Unfoldings.Cap.ProjectedDevelopedMap
public import Unfoldings.Cap.SectionInteriors
public import Unfoldings.Geometry.SharedEdgeInterior

/-! Retained physical fine seams inside a single original input face. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.LineAlignedClip

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (L : K.LineAlignedClip Z K.originalEdgeEquations)

local instance originalRetentionIndexFintype : Fintype L.partition.Index :=
  @Fintype.ofFinite _ L.partition.finite

open Classical in
def originalRetain (retain : Set C.Seam) : Set L.originalComplex.Seam :=
  L.partition.pairedComplex.restrictRetain L.originalPieceSet
    (L.partition.retainOutside (K.projectedCutSet retain))

open Classical in
theorem original_seam_kept_of_same_parent (retain : Set C.Seam)
    (s : L.originalComplex.Seam)
    (same : L.originalParent (L.originalComplex.left s).face =
      L.originalParent (L.originalComplex.right s).face) :
    s ∈ L.originalRetain retain := by
  let a := (L.originalComplex.left s).face
  let b := (L.originalComplex.right s).face
  have different : a.val ≠ b.val :=
    (TriangleFamily.seamPair L.partition.projectedTriangle s.val).different_faces
  have shared := L.partition.paired_seam_projected_edge s.val
  obtain ⟨x, regular⟩ := (L.partition.projectedTriangle a.val).exists_edge_nonvertex
    (L.originalComplex.left s).edge
  have inside : x.val ∈ interior (K.projectedTriangle (L.originalParent a)).carrier :=
    (L.partition.projectedTriangle a.val).shared_edge_mem_interior_of_subsets
      (L.partition.projectedTriangle b.val) _ _ shared
      (L.partition.separated different) (L.originalParent_contains a)
      (by simpa only [show L.originalParent a = L.originalParent b from same] using
        L.originalParent_contains b) x regular
  intro selected
  obtain ⟨t, member⟩ := Set.mem_iUnion.mp (selected x.property)
  obtain ⟨_cut, member⟩ := Set.mem_iUnion.mp member
  exact K.projected_seam_not_mem_face_interior t (L.originalParent a) inside member

end Unfoldings.ConvexCap.LineAlignedClip
