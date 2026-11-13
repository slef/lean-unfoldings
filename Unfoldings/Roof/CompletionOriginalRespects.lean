module

public import Unfoldings.Roof.CompletionOriginalRetention
public import Unfoldings.Roof.CompletionOriginalAdjacency
public import Unfoldings.Roof.ProjectedPointCopies

/-! Every retained fine seam maps to an actual retained original seam chain. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (L : K.CompletionMesh φ region K.originalEdgeEquations)

local instance originalRespectsIndexFintype : Fintype L.partition.Index :=
  @Fintype.ofFinite _ L.partition.finite

open Classical in
theorem originalSubdivision_pointCopy (retain : Set C.Seam)
    (i : L.originalPieceSet) (y : L.originalComplex.Cell i) :
    K.pointCopy retain (L.originalParent i) (L.pieceProjection (i.val) y.val)
        (L.originalParent_contains i (L.partition.projected_member i.val y.property)) =
      C.faceMap retain (L.originalParent i) ((L.originalSubdivision).parentCell i y) := rfl

open Classical in
theorem originalSubdivision_respects (retain : Set C.Seam)
    (a b : L.originalComplex.Total)
    (joined : L.originalComplex.glue (L.originalRetain retain) a b) :
    Relation.EqvGen (C.glue retain) ((L.originalSubdivision).parentPoint a)
      ((L.originalSubdivision).parentPoint b) := by
  obtain ⟨s, kept, x, rfl, rfl⟩ := joined
  apply (C.faceMap_eq_iff retain _ _ _ _).mp
  change C.faceMap retain (L.originalParent (L.originalComplex.left s).face)
      ((L.originalSubdivision).parentCell (L.originalComplex.left s).face
        ((L.originalComplex.triangle _).edgeMap _ x)) =
    C.faceMap retain (L.originalParent (L.originalComplex.right s).face)
      ((L.originalSubdivision).parentCell (L.originalComplex.right s).face
        ((L.originalComplex.triangle _).edgeMap _ (L.originalComplex.identify s x)))
  rw [← L.originalSubdivision_pointCopy, ← L.originalSubdivision_pointCopy]
  have physical := L.partition.paired_seam_projection s.val x
  change L.pieceProjection ((L.originalComplex.right s).face.val)
      (L.originalComplex.identify s x).val =
    L.pieceProjection ((L.originalComplex.left s).face.val) x.val at physical
  change K.pointCopy retain _
      (L.pieceProjection (L.originalComplex.left s).face.val x.val) _ =
    K.pointCopy retain _ (L.pieceProjection (L.originalComplex.right s).face.val
      (L.originalComplex.identify s x).val) _
  by_cases same : L.originalParent (L.originalComplex.left s).face =
      L.originalParent (L.originalComplex.right s).face
  · have copies (f g : Face) (equal : f = g) (p q : Plane) (point : p = q)
        (first : p ∈ (K.projectedTriangle f).carrier)
        (last : q ∈ (K.projectedTriangle g).carrier) :
        K.pointCopy retain f p first = K.pointCopy retain g q last := by
      subst g
      subst q
      rfl
    exact copies _ _ same _ _ physical.symm _ _
  · simp only [ConvexRoof.pointCopy, physical]
    obtain ⟨e, f, shared, contained⟩ := L.original_seam_parent_edge s same
    have uncut : ¬ (K.projectedTriangle
        (L.originalParent (L.originalComplex.left s).face)).edge e ⊆
          K.projectedCutSet retain := by
      intro selected
      exact kept (contained.trans selected)
    exact K.pointCopy_eq_of_shared_edge retain
      (a := ⟨L.originalParent (L.originalComplex.left s).face, e⟩)
      (b := ⟨L.originalParent (L.originalComplex.right s).face, f⟩) same shared uncut
      (contained ((L.partition.edgeProjection
        (L.originalComplex.left s).face.val (L.originalComplex.left s).edge) x).property)

end Unfoldings.ConvexRoof.CompletionMesh
