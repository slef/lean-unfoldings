module

public import Unfoldings.Roof.CompletionProjectedSubdivision
public import Unfoldings.Roof.CompletionProjectedFaceAngles
public import Unfoldings.Roof.CompletionProjectedFacePatch
public import Unfoldings.Complex.AffineProjectionSubdivision
public import Unfoldings.Complex.AffineProjectionSubdivisionVertices
public import Unfoldings.Development.AffineProjectionEmbedding

/-! Each original projected corner retains its exact angle in the physical completion. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionProjectedSubdivisionAnglesIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
def facePieceProjectedCornerEquiv (f : Face) : (E.facePieceProjectedComplex f).Corner ≃
    {d : E.originalProjectedComplex.Corner // E.originalParent d.1 = f} :=
  E.facePieceCornerEquiv f

open Classical in
/-- Fine projected angles sum to the old projected angle at every named old corner. -/
theorem originalProjectedSubdivision_cornerAnglePreserving :
    E.originalProjectedSubdivision.CornerAnglePreserving := by
  classical
  rintro ⟨f, k⟩
  have triangle : K.projectedMetricComplex.triangle f = K.projectedTriangle f := by
    apply Triangle.eq_of_vertex_eq
    intro i
    rfl
  let weight (d : E.originalProjectedComplex.Corner) : ℝ :=
    if (E.originalProjectedComplex.triangle d.1).vertex d.2 =
        (K.projectedTriangle f).vertex k then
      (E.originalProjectedComplex.triangle d.1).cornerAngle d.2 else 0
  calc
    _ = ∑ d : E.originalProjectedComplex.Corner,
        if E.originalParent d.1 = f then weight d else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases parent : E.originalParent d.1 = f <;>
        simp [TriangleComplex.Subdivision.RefinesCorner, originalProjectedSubdivision,
          TriangleComplex.Subdivision.affineProjectionSubdivision, originalSubdivision,
          triangle, weight, parent]; rfl
    _ = ∑ d : {d : E.originalProjectedComplex.Corner // E.originalParent d.1 = f},
        weight d.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) weight
    _ = ∑ c : (E.facePieceProjectedComplex f).Corner,
        weight (E.facePieceProjectedCornerEquiv f c).val :=
      (Equiv.sum_comp (E.facePieceProjectedCornerEquiv f) (fun d => weight d.val)).symm
    _ = (K.projectedTriangle f).cornerAngle k := by
      convert E.facePieceProjected_sum_cornerAngles f k using 1
      apply Finset.sum_congr rfl
      intro c _
      rfl

open Classical in
/-- The corresponding original cut-side fan retains its exact projected angle. -/
theorem original_projectedTotalAngle_eq (retain : Set C.Seam)
    (fine : E.originalComplex.Vertex (E.originalRetain retain)) (coarse : C.Vertex retain)
    (same : E.originalMetricEquiv retain
      (E.originalComplex.vertexPoint (E.originalRetain retain) fine) =
        C.vertexPoint retain coarse) :
    E.originalProjectedComplex.totalAngle (E.originalRetain retain)
      (E.originalComplex.affineProjectionVertexEquiv E.originalProjection
        E.originalProjection_joined (E.originalRetain retain) fine) =
      K.projectedTotalAngle retain coarse := by
  let HP := E.originalProjectedSubdivision_conforming retain
  have matched := E.originalSubdivision.affineProjectionSubdivision_vertexPoint
    K.projectFaceEquiv K.projectedTriangle_joined E.originalProjection
    E.originalProjection_joined E.originalSubdivision_projection
    (E.originalSubdivision_conforming retain) fine coarse same
  have angle := HP.totalAngle_eq_of_vertexPoint
    E.originalProjectedSubdivision_cornerAnglePreserving _ _ matched
  exact angle.trans (C.affineProjection_totalAngle K.projectFaceEquiv
    K.projectedTriangle_joined retain coarse)

end Unfoldings.ConvexRoof.CompletionMesh
