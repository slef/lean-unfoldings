module

public import Unfoldings.Roof.CompletionSubdivisionAngles
public import Unfoldings.Complex.RetainedFanSubdivision

/-! Physical roof completions preserve every actual original one-sided retained fan angle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionRetainedFanAnglesIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- The physical completion supplies angle preservation itself. Its actual fine corners
on the chosen original face side carry exactly the original retained vertex-copy angle.
No regional angle equality or fan-angle preservation certificate is supplied. -/
theorem original_retainedFan_angle (retain : Set C.Seam) (vertex : C.Vertex retain) :
    (∑ d : E.originalComplex.Corner,
      if E.originalParent d.1 ∈ C.retainedFanFaces retain vertex ∧
        MetricGluing.point C.Cell (C.glue Set.univ)
          (E.originalSubdivision.parentPoint (E.originalComplex.cornerPoint d)) =
            C.vertexPoint Set.univ (C.vertexForgetCuts (Set.subset_univ retain) vertex)
      then (E.originalComplex.triangle d.1).cornerAngle d.2 else 0) =
        C.totalAngle retain vertex :=
  K.folding.sum_refined_retainedFan_angles E.originalSubdivision
    E.originalSubdivision_cornerAnglePreserving retain vertex

end Unfoldings.ConvexRoof.CompletionMesh
