module

public import Unfoldings.Cap.JordanBankPositions
public import Unfoldings.Cap.RestrictedBankSegments
public import Unfoldings.Complex.BoundaryContourPaths

/-! The actual Jordan curve is precisely its consecutive physical contour segments. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- The contour's cyclic successor is the genuine far endpoint of its physical bank. -/
theorem jordanContour_directed_path_projection
    (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) (t : unitInterval) :
    K.toRoof.restrictProjection (K.jordanFaces J)
        ((C.restrictFaces (K.jordanFaces J)).directedBoundaryPath
          ((K.jordanContour jordan contains avoids).cycle.point i) t) =
      AffineMap.lineMap (K.jordanBankPosition jordan contains avoids i)
        (K.jordanBankPosition jordan contains avoids
          (finRotate ((K.jordanContour jordan contains avoids).length + 1) i)) t.val := by
  let R := C.restrictFaces (K.jordanFaces J)
  let F := K.folding.restrictFaces (K.jordanFaces J)
  let Q := K.jordanContour jordan contains avoids
  rw [K.restrictProjection_directedBoundaryPath,
    F.germDirection_boundary_step (Q.next_cyclic R i), map_sub,
    AffineMap.lineMap_apply_module']
  exact add_comm _ _

include jordan contains avoids in
open Classical in
/-- No geometric arc or boundary bank is missing from the actual cyclic segment cover. -/
theorem jordanCurve_eq_contour_segments :
    J = ⋃ i : Fin ((K.jordanContour jordan contains avoids).length + 1),
      segment ℝ (K.jordanBankPosition jordan contains avoids i)
        (K.jordanBankPosition jordan contains avoids
          (finRotate ((K.jordanContour jordan contains avoids).length + 1) i)) := by
  ext p
  constructor
  · intro member
    have in_filling : p ∈ PlanarTopology.closedJordanDomain J := by
      rw [← PlanarTopology.frontier_closedJordanDomain jordan] at member
      exact (closure_eq_iff_isClosed.mpr isClosed_closure).subset
        (frontier_subset_closure member)
    obtain ⟨x, equal⟩ := (K.jordanIntrinsicHomeomorph jordan contains avoids).surjective
      ⟨p, in_filling⟩
    have projected : K.toRoof.restrictProjection (K.jordanFaces J) x = p :=
      congrArg Subtype.val equal
    have boundary := (K.jordan_bankBoundary_iff jordan contains avoids x).mpr
      (projected ▸ member)
    obtain ⟨i, t, same⟩ := (K.jordanContour jordan contains avoids).exists_directedBoundaryPath
      (C.restrictFaces (K.jordanFaces J)) boundary
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [segment_eq_image_lineMap]
    refine ⟨t.val, t.property, ?_⟩
    exact (K.jordanContour_directed_path_projection jordan contains avoids i t).symm.trans
      ((congrArg (K.toRoof.restrictProjection (K.jordanFaces J)) same).trans projected)
  · intro member
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp member
    rw [segment_eq_image_lineMap] at member
    obtain ⟨t, ht, rfl⟩ := member
    rw [← K.jordanContour_directed_path_projection jordan contains avoids i ⟨t, ht⟩]
    exact (K.jordan_bankBoundary_iff jordan contains avoids _).mp
      ((C.restrictFaces (K.jordanFaces J)).directedBoundaryPath_mem_boundary _ _)

include jordan contains avoids in
open Classical in
/-- A contour bank's open segment contains no other actual contour vertex. -/
theorem jordanBankPosition_not_mem_open_contour_segment
    (i j : Fin ((K.jordanContour jordan contains avoids).length + 1)) :
    K.jordanBankPosition jordan contains avoids j ∉ openSegment ℝ
      (K.jordanBankPosition jordan contains avoids i)
      (K.jordanBankPosition jordan contains avoids
        (finRotate ((K.jordanContour jordan contains avoids).length + 1) i)) := by
  intro member
  rw [openSegment_eq_image_lineMap] at member
  obtain ⟨t, ht, equal⟩ := member
  let R := C.restrictFaces (K.jordanFaces J)
  let Q := K.jordanContour jordan contains avoids
  let w := R.boundaryEndVertex Set.univ (Q.cycle.point j)
  have vertex_projection : K.toRoof.restrictProjection (K.jordanFaces J)
      (R.vertexPoint Set.univ w) = K.jordanBankPosition jordan contains avoids j := rfl
  have same : K.toRoof.restrictProjection (K.jordanFaces J)
      (R.directedBoundaryPath (Q.cycle.point i) ⟨t, ht.1.le, ht.2.le⟩) =
        K.toRoof.restrictProjection (K.jordanFaces J) (R.vertexPoint Set.univ w) := by
    rw [K.jordanContour_directed_path_projection, vertex_projection]
    exact equal
  have intrinsic := (K.jordanIntrinsicHomeomorph jordan contains avoids).injective
    (Subtype.ext same)
  exact R.directedBoundaryPath_ne_vertexPoint (Q.cycle.point i) _ ht.1 ht.2 w intrinsic

include jordan contains avoids in
open Classical in
/-- Every original physical vertex on the curve appears at its actual contour position. -/
theorem exists_jordanBankPosition_of_projected_vertex (w : C.Vertex Set.univ)
    (on_curve : K.projectedVertex w ∈ J) :
    ∃ i, K.jordanBankPosition jordan contains avoids i = K.projectedVertex w := by
  obtain ⟨i, same⟩ := (K.jordanContourVertexEquiv jordan contains avoids).surjective
    ⟨w, on_curve⟩
  refine ⟨i, ?_⟩
  have projected := congrArg (fun x => K.projectedVertex x.val) same
  exact (K.projected_restricted_boundaryPosition (K.jordanFaces J) _).symm.trans projected

end Unfoldings.ConvexCap
