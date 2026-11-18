module

public import Unfoldings.Complex.ContourParentBanks
public import Unfoldings.Polyhedron.DirectedBankMetric

/-! The original contour's two rootward banks have the same actual physical interpolation. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) {retain : Set C.Seam}

/-- Cut-side boundary positions restore to their exact original spatial vertex. -/
theorem boundaryPosition_original_vertex (p : C.BoundaryEnd retain) :
    F.boundaryPosition p = F.toSpace Set.univ (C.vertexPoint Set.univ
      (C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex _ p))) := by
  rw [C.vertexPoint_vertexForgetCuts, F.toSpace_forgetCuts]
  rfl

include F in
/-- The original bank's full length is its intrinsic interval speed, including endpoints. -/
theorem edist_directedBoundaryPath_eq_length (p : C.BoundaryEnd retain)
    (s t : unitInterval) :
    edist (C.directedBoundaryPath p s) (C.directedBoundaryPath p t) =
      ENNReal.ofReal (C.boundaryBankLength p) * edist s t := by
  rw [F.edist_directedBoundaryPath_eq_spatial, F.directedBoundaryPath_position,
    F.directedBoundaryPath_position, edist_dist, edist_dist]
  change ENNReal.ofReal (dist
    (F.boundaryPosition p + s.val • F.germDirection p.val)
    (F.boundaryPosition p + t.val • F.germDirection p.val)) =
    ENNReal.ofReal (C.boundaryBankLength p) * ENNReal.ofReal (dist s.val t.val)
  rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs,
    ENNReal.ofReal_mul (abs_nonneg _), mul_comm, F.boundaryBankLength_eq_germDirection_norm]
  rfl

variable {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (roots : C.relativeCutRoots Set.univ ⊆ P.roots)
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)
  (vertex : C.Vertex Set.univ) (nonroot : vertex ∉ P.roots)

/-- Both actual oriented copies have the same physical child-to-parent vector. -/
theorem contourParentBank_direction (side : Bool) :
    F.germDirection (C.contourParentBank S Q roots starts vertex nonroot side).val =
      F.toSpace Set.univ (C.vertexPoint Set.univ (P.parent vertex)) -
        F.toSpace Set.univ (C.vertexPoint Set.univ vertex) := by
  rw [F.germDirection_boundary_positions, F.boundaryPosition_original_vertex,
    F.boundaryPosition_original_vertex, C.contourParentBank_start,
    C.contourParentBank_finish]

/-- Both closed bank copies interpolate the very same original spatial parent edge. -/
theorem contourParentBank_position (side : Bool) (t : unitInterval) :
    F.toSpace (C.selectedRetain S)
      (C.directedBoundaryPath (C.contourParentBank S Q roots starts vertex nonroot side) t) =
      AffineMap.lineMap (F.toSpace Set.univ (C.vertexPoint Set.univ vertex))
        (F.toSpace Set.univ (C.vertexPoint Set.univ (P.parent vertex))) t.val := by
  rw [F.directedBoundaryPath_position, F.contourParentBank_direction S Q roots starts,
    F.boundaryPosition_original_vertex, C.contourParentBank_start,
    AffineMap.lineMap_apply_module']
  exact add_comm _ _

include F in
/-- The two literal contour-side paths have equal intrinsic edge distances. -/
theorem edist_contourParentBank_sides (s t : unitInterval) :
    edist (C.directedBoundaryPath (C.contourParentBank S Q roots starts vertex nonroot false) s)
      (C.directedBoundaryPath (C.contourParentBank S Q roots starts vertex nonroot false) t) =
    edist (C.directedBoundaryPath (C.contourParentBank S Q roots starts vertex nonroot true) s)
      (C.directedBoundaryPath (C.contourParentBank S Q roots starts vertex nonroot true) t) := by
  rw [F.edist_directedBoundaryPath_eq_spatial, F.edist_directedBoundaryPath_eq_spatial,
    F.contourParentBank_position S Q roots starts,
    F.contourParentBank_position S Q roots starts,
    F.contourParentBank_position S Q roots starts,
    F.contourParentBank_position S Q roots starts]

end Unfoldings.SpatialFolding
