module

public import Unfoldings.Roof.CompletionFaceAngles
public import Unfoldings.Roof.CompletionOriginalConforming
public import Unfoldings.Complex.SubdivisionCornerAngles

/-! The actual physical completion preserves every original corner angle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionSubdivisionAnglesIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- Corners of a physical face patch are exactly the original pieces with that parent. -/
def facePieceCornerEquiv (f : Face) : (E.facePieceComplex f).Corner ≃
    {d : E.originalComplex.Corner // E.originalParent d.1 = f} where
  toFun c := ⟨(⟨c.1.val, f, c.1.property⟩, c.2),
    E.originalParent_eq _ c.1.property⟩
  invFun d := (⟨d.val.1.val, by
    have contained := E.originalParent_contains d.val.1
    rwa [d.property] at contained⟩, d.val.2)
  left_inv _ := rfl
  right_inv _ := rfl

open Classical in
/-- Fine-corner angles over each old corner sum to its original Euclidean angle. -/
theorem originalSubdivision_cornerAnglePreserving :
    E.originalSubdivision.CornerAnglePreserving := by
  classical
  rintro ⟨f, k⟩
  let weight (d : E.originalComplex.Corner) : ℝ :=
    if E.originalSubdivision.place d.1 ((E.originalComplex.triangle d.1).vertex d.2) =
        (C.triangle f).vertex k then (E.originalComplex.triangle d.1).cornerAngle d.2 else 0
  calc
    _ = ∑ d : E.originalComplex.Corner, if E.originalParent d.1 = f then weight d else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases parent : E.originalParent d.1 = f <;>
        simp [TriangleComplex.Subdivision.RefinesCorner, originalSubdivision, weight, parent]
    _ = ∑ d : {d : E.originalComplex.Corner // E.originalParent d.1 = f}, weight d.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) weight
    _ = ∑ c : (E.facePieceComplex f).Corner, weight (E.facePieceCornerEquiv f c).val :=
      (Equiv.sum_comp (E.facePieceCornerEquiv f) (fun d => weight d.val)).symm
    _ = (C.triangle f).cornerAngle k := by
      convert E.facePiece_sum_cornerAngles f k using 1
      apply Finset.sum_congr rfl
      intro c _
      have parent := E.originalParent_eq (⟨c.1.val, f, c.1.property⟩ : E.originalPieceSet)
        c.1.property
      change (if E.originalCoordinates c.1.val
          (E.originalParent ⟨c.1.val, f, c.1.property⟩)
          ((E.partition.triangle c.1.val).vertex c.2) = (C.triangle f).vertex k
        then (E.partition.triangle c.1.val).cornerAngle c.2 else 0) =
        (if E.originalCoordinates c.1.val f ((E.partition.triangle c.1.val).vertex c.2) =
          (C.triangle f).vertex k then (E.partition.triangle c.1.val).cornerAngle c.2 else 0)
      rw [parent]

open Classical in
/-- Every original cut vertex copy has exactly one physical fine vertex above it. -/
theorem existsUnique_original_vertex (retain : Set C.Seam) (coarse : C.Vertex retain) :
    ∃! fine : E.originalComplex.Vertex (E.originalRetain retain),
      E.originalMetricEquiv retain
        (E.originalComplex.vertexPoint (E.originalRetain retain) fine) =
          C.vertexPoint retain coarse :=
  (E.originalSubdivision_conforming retain).existsUnique_vertex_over
    E.originalSubdivision_cornerAnglePreserving coarse

open Classical in
/-- Actual fine cut fans preserve the corresponding original one-sided fan angles exactly. -/
theorem original_totalAngle_eq (retain : Set C.Seam)
    (fine : E.originalComplex.Vertex (E.originalRetain retain)) (coarse : C.Vertex retain)
    (same : E.originalMetricEquiv retain
      (E.originalComplex.vertexPoint (E.originalRetain retain) fine) =
        C.vertexPoint retain coarse) :
    E.originalComplex.totalAngle (E.originalRetain retain) fine = C.totalAngle retain coarse :=
  (E.originalSubdivision_conforming retain).totalAngle_eq_of_vertexPoint
    E.originalSubdivision_cornerAnglePreserving fine coarse same

end Unfoldings.ConvexRoof.CompletionMesh
