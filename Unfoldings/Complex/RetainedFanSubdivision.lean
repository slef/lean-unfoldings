module

public import Unfoldings.Complex.RetainedFanFaces
public import Unfoldings.Complex.SubdivisionWeightedAngles

/-! Geometric refinement preserves a selected actual one-sided retained fan's original angle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v w z

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {Child : Type w} [Fintype Child] {D : TriangleComplex.{w, z} Child}
  (S : C.Subdivision D) (preserving : S.CornerAnglePreserving)
  (retain : Set C.Seam) (vertex : C.Vertex retain)

include F preserving in
open Classical in
/-- Select fine corners by their actual original face side and physical original vertex.
Their intrinsic angles sum to exactly the chosen original cut-copy angle, rather than
summing contributions from all copies of that original vertex. -/
theorem sum_refined_retainedFan_angles :
    (∑ d : D.Corner, if S.parent d.1 ∈ C.retainedFanFaces retain vertex ∧
      MetricGluing.point C.Cell (C.glue Set.univ) (S.parentPoint (D.cornerPoint d)) =
        C.vertexPoint Set.univ (C.vertexForgetCuts (Set.subset_univ retain) vertex)
      then (D.triangle d.1).cornerAngle d.2 else 0) = C.totalAngle retain vertex :=
  (S.sum_angles_over_parent_vertex_in_faces preserving (C.retainedFanFaces retain vertex)
    (C.vertexForgetCuts (Set.subset_univ retain) vertex)).trans
      (F.totalAngle_eq_regional_retainedFanFaces retain vertex).symm

end Unfoldings.SpatialFolding
