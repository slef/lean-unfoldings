module

public import Unfoldings.Cap.ClipSpatialTriangles
public import Unfoldings.Geometry.CommonTriangleRefinement

/-! The actual clipped-roof triangle partition refined with one shared geometric boundary graph. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.ClipSpatialTriangles

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

def commonRefinement : CommonTriangleRefinement T.projectedTriangle :=
  let := T.finite
  commonTriangleRefinement T.projectedTriangle

/-- Exact roof coverage, rigid supporting-face maps, and normals survive the common refinement. -/
def refined : K.ClipSpatialTriangles Z where
  Index := T.commonRefinement.Index
  finite := by
    let := T.finite
    infer_instance
  projectedTriangle := T.commonRefinement.triangle
  face j := T.face j.1
  cover := T.cover.trans T.commonRefinement.total_cover
  separated := T.commonRefinement.separated T.separated
  active j p member := T.active j.1 p (T.commonRefinement.triangle_subset j member)

end Unfoldings.ConvexCap.ClipSpatialTriangles
