module

public import Unfoldings.Cap.JordanFanAngles
public import Unfoldings.Complex.BoundaryContour
public import Unfoldings.Complex.DiskCuts
public import Unfoldings.Complex.RelativeSeamGeometry

/-! The intrinsic Jordan disk has exactly the actual geometric curve as its bank boundary. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- No intrinsic boundary bank is lost or added by the geometric Jordan filling. -/
theorem jordan_bankBoundary_iff
    (x : (C.restrictFaces (K.jordanFaces J)).Realization Set.univ) :
    x ∈ (C.restrictFaces (K.jordanFaces J)).bankBoundary Set.univ ↔
      K.toRoof.restrictProjection (K.jordanFaces J) x ∈ J := by
  obtain ⟨F, image⟩ := PlanarTopology.exists_ambient_closedJordanDomain_disk jordan
  let disk := (K.jordanIntrinsicHomeomorph jordan contains avoids).trans
    ((F.image (PlanarTopology.closedJordanDomain J)).trans (Homeomorph.setCongr image))
  rw [(K.folding.restrictFaces (K.jordanFaces J)).bankBoundary_iff_disk_norm_eq_one
    Set.univ disk x]
  change ‖F (K.toRoof.restrictProjection (K.jordanFaces J) x)‖ = 1 ↔ _
  have boundary_image : F '' J = Metric.sphere (0 : Plane) 1 := by
    rw [← PlanarTopology.frontier_closedJordanDomain jordan, F.image_frontier, image,
      frontier_closedBall (0 : Plane) (by norm_num : (1 : ℝ) ≠ 0)]
  rw [← mem_sphere_zero_iff_norm, ← boundary_image]
  exact F.injective.mem_set_image

include jordan contains avoids in
open Classical in
/-- An actual restricted vertex is a boundary copy exactly when its original vertex is on J. -/
theorem jordan_isBoundaryVertex_iff
    (w : (C.restrictFaces (K.jordanFaces J)).Vertex Set.univ) :
    (C.restrictFaces (K.jordanFaces J)).IsBoundaryVertex Set.univ w ↔
      K.projectedVertex (C.includeRestrictedVertexUniv (K.jordanFaces J) w) ∈ J := by
  rw [← (C.restrictFaces (K.jordanFaces J)).vertexPoint_mem_bankBoundary_iff,
    K.jordan_bankBoundary_iff jordan contains avoids,
    ← K.projected_includeRestrictedVertex]

open Classical in
/-- The complete actual bank cycle of the constructed intrinsic Jordan disk. -/
def jordanContour : (C.restrictFaces (K.jordanFaces J)).BoundaryContour Set.univ :=
  (C.restrictFaces (K.jordanFaces J)).boundaryContourOfConnected Set.univ
    ((K.folding.restrictFaces (K.jordanFaces J)).boundaryGraph_connected_of_disk Set.univ
      (K.jordanIntrinsicDisk jordan contains avoids))

end Unfoldings.ConvexCap
