module

public import Unfoldings.Cap.ClipOriginalNonoverlap
public import Unfoldings.Cap.ClippedCapCoordinates
public import Unfoldings.Cap.ProjectedDenseSeparation
public import Unfoldings.Development.FaceRestriction
public import Unfoldings.Development.AdditionalCuts

/-! Local roof-face separation over the whole original footprint proves original-cap nonoverlap. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.LineAlignedClip

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (L : K.LineAlignedClip Z K.originalEdgeEquations)

local instance originalLocalSeparationIndexFintype : Fintype L.partition.Index :=
  @Fintype.ofFinite _ L.partition.finite

open Classical in
theorem original_nonoverlap_of_local_roof_separation (lower : Z < 0) (retain : Set C.Seam)
    [PreconnectedSpace (C.Realization retain)]
    (fineRetain : Set L.partition.pairedComplex.Seam)
    (D : FacewiseDevelopment L.partition.pairedComplex fineRetain)
    (inclusion : L.originalRetain retain ⊆
      L.partition.pairedComplex.restrictRetain L.originalPieceSet fineRetain)
    (U : Set Plane) (cover : K.footprint ⊆ U)
    (separate : let Q := L.partition.normalizedCap L.conforming lower
      Pairwise (fun f g => Disjoint
        (D.projectedPlacement Q f '' (interior (Q.projectedTriangle f).carrier ∩ U))
        (D.projectedPlacement Q g '' (interior (Q.projectedTriangle g).carrier ∩ U))))
    (E : FacewiseDevelopment C retain) : E.Nonoverlapping := by
  let Q := L.partition.normalizedCap L.conforming lower
  change Pairwise (fun f g => Disjoint
    (D.projectedPlacement Q f '' (interior (Q.projectedTriangle f).carrier ∩ U))
    (D.projectedPlacement Q g '' (interior (Q.projectedTriangle g).carrier ∩ U))) at separate
  let A : FacewiseDevelopment L.originalComplex (L.originalRetain retain) :=
    (D.restrictFaces L.originalPieceSet).cut inclusion
  have inside (i : L.originalPieceSet) : interior (Q.projectedTriangle i.val).carrier ⊆ U := by
    intro p member
    apply cover
    rw [K.footprint_eq_union_projectedTriangles]
    apply Set.mem_iUnion.mpr
    refine ⟨L.originalParent i, L.originalParent_contains i ?_⟩
    exact (L.partition.normalizedCap_projectedTriangle_carrier L.conforming lower i.val).subset
      (interior_subset member)
  have nonoverlap : A.Nonoverlapping := by
    intro i j different
    change Disjoint (interior (D.faceImage i.val)) (interior (D.faceImage j.val))
    rw [← D.projectedPlacement_image_interior Q, ← D.projectedPlacement_image_interior Q]
    have first : interior (Q.projectedTriangle i.val).carrier ∩ U =
        interior (Q.projectedTriangle i.val).carrier := Set.inter_eq_left.mpr (inside i)
    have last : interior (Q.projectedTriangle j.val).carrier ∩ U =
        interior (Q.projectedTriangle j.val).carrier := Set.inter_eq_left.mpr (inside j)
    simpa only [first, last] using separate (fun equal => different (Subtype.ext equal))
  exact (L.originalDevelopment_nonoverlapping_iff lower retain E A).mp nonoverlap

end Unfoldings.ConvexCap.LineAlignedClip
