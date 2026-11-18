module

public import Unfoldings.Roof.CompletionProjectedInsertedAngles
public import Unfoldings.Complex.AffineProjectionSubdivisionPoints
public import Unfoldings.Roof.CompletionBankRolling

/-! Every inserted original-bank fan is straight in the actual projected metric as well. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionProjectedBankFansIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

open Classical in
/-- The original retained copy identifies the exact straight projected cut-side fan. -/
theorem original_projected_fan_at_bank_interior (retain : Set C.Seam)
    (bank : C.BoundaryBank retain)
    (x : (C.triangle bank.val.face).Edge bank.val.edge)
    (regular : ¬ C.IsVertex (C.edgePoint bank.val x))
    (fine : E.originalComplex.Vertex (E.originalRetain retain))
    (at_point : E.originalMetricEquiv retain
      (E.originalComplex.vertexPoint (E.originalRetain retain) fine) = C.bankMap retain bank x) :
    E.originalProjectedComplex.totalAngle (E.originalRetain retain)
      (E.originalComplex.affineProjectionVertexEquiv E.originalProjection
        E.originalProjection_joined (E.originalRetain retain) fine) = Real.pi := by
  let P := K.projectedMetricComplex
  let projectedBank : P.BoundaryBank retain := ⟨bank.val, bank.property⟩
  let projectedPoint : (P.triangle bank.val.face).Edge bank.val.edge :=
    ⟨K.projectFaceEquiv bank.val.face x.val, by
      exact ((C.triangle bank.val.face).affineImage_edge
        (K.projectFaceEquiv bank.val.face).toAffineMap
        (K.projectFaceEquiv bank.val.face).injective bank.val.edge).symm.subset
          ⟨x.val, x.property, rfl⟩⟩
  have projectedRegular : ¬ P.IsVertex (P.edgePoint bank.val projectedPoint) := by
    rintro ⟨k, equal⟩
    apply regular
    exact ⟨k, (K.projectFaceEquiv bank.val.face).injective equal⟩
  obtain ⟨d, rfl⟩ := E.originalComplex.vertexOfCorner_surjective (E.originalRetain retain) fine
  have transported := E.originalSubdivision.affineProjectionSubdivision_point
    K.projectFaceEquiv K.projectedTriangle_joined E.originalProjection
    E.originalProjection_joined E.originalSubdivision_projection
    (E.originalSubdivision_conforming retain) (E.originalComplex.cornerPoint d)
    (C.edgePoint bank.val x) at_point
  exact E.original_projected_totalAngle_at_bank_interior retain projectedBank projectedPoint
    projectedRegular _ transported

open Classical in
/-- An actual bank end strictly between old bank endpoints has a straight projected fan. -/
theorem original_projected_bankEnd_totalAngle_at_open_bank (retain : Set C.Seam)
    (coarse : C.BoundaryBank retain)
    (p : E.originalComplex.BoundaryEnd (E.originalRetain retain))
    (parent : E.originalParent p.val.1.1 = coarse.val.face)
    {t : ℝ} (positive : 0 < t) (small : t < 1)
    (position : E.originalBankEndProjection p =
      AffineMap.lineMap ((K.projectedTriangle coarse.val.face).vertex coarse.val.edge)
        ((K.projectedTriangle coarse.val.face).vertex (Triangle.next coarse.val.edge)) t) :
    E.originalProjectedComplex.totalAngle (E.originalRetain retain)
      (E.originalComplex.affineProjectionVertexEquiv E.originalProjection
        E.originalProjection_joined (E.originalRetain retain)
        (E.originalComplex.boundaryEndVertex (E.originalRetain retain) p)) = Real.pi := by
  let D := E.originalComplex
  let kept := E.originalRetain retain
  let fine := (D.boundaryEndEquiv kept p).1
  let flag := (D.boundaryEndEquiv kept p).2
  let x := (D.triangle fine.val.face).endpoint fine.val.edge flag
  let y : (C.triangle coarse.val.face).Edge coarse.val.edge :=
    ⟨_, lineMap_mem_segment ℝ _ _ ⟨positive.le, small.le⟩⟩
  have y_regular : ¬ C.IsVertex (C.edgePoint coarse.val y) :=
    (C.triangle coarse.val.face).lineMap_edge_not_vertex coarse.val.edge ⟨positive, small⟩
  have projected : E.pieceProjection fine.val.face.val x.val =
      K.projectFace coarse.val.face y.val := by
    have equal : E.pieceProjection fine.val.face.val x.val = E.originalBankEndProjection p := by
      change E.pieceProjection fine.val.face.val
        ((D.triangle fine.val.face).endpoint fine.val.edge flag).val = _
      obtain ⟨⟨bank, side⟩, rfl⟩ := (D.boundaryEndEquiv kept).symm.surjective p
      rcases bank with ⟨⟨face, edge⟩, boundary⟩
      cases side <;> fin_cases edge <;> rfl
    rw [equal, position]
    exact ((K.projectFace coarse.val.face).apply_lineMap _ _ t).symm
  have at_point := E.originalMetricEquiv_bank_point retain fine coarse parent x y projected
  rw [← D.boundaryEnd_vertexPoint_eq_endpoint p] at at_point
  exact E.original_projected_fan_at_bank_interior retain coarse y y_regular
    (D.boundaryEndVertex kept p) at_point


open Classical in
/-- A physical point strictly inside a directed old bank has its actual straight projected fan. -/
theorem original_projected_fan_at_directed_bank_point {retain : Set C.Seam}
    (p : E.originalComplex.BoundaryEnd (E.originalRetain retain))
    (q : C.BoundaryEnd retain) (t : unitInterval) (positive : 0 < t.val) (small : t.val < 1)
    (parent : E.originalParent p.val.1.1 = (C.boundaryEndEquiv retain q).1.val.face)
    (position : E.originalBankEndProjection p =
      Cap.horizontal (K.folding.toSpace retain (C.directedBoundaryPath q t))) :
    E.originalProjectedComplex.totalAngle (E.originalRetain retain)
      (E.originalComplex.affineProjectionVertexEquiv E.originalProjection
        E.originalProjection_joined (E.originalRetain retain)
        (E.originalComplex.boundaryEndVertex (E.originalRetain retain) p)) = Real.pi := by
  let D := E.originalComplex
  let kept := E.originalRetain retain
  let fine := (D.boundaryEndEquiv kept p).1
  let flag := (D.boundaryEndEquiv kept p).2
  let x := (D.triangle fine.val.face).endpoint fine.val.edge flag
  let bank := (C.boundaryEndEquiv retain q).1
  let y := C.bankParameterFromEnd bank (C.boundaryEndEquiv retain q).2 t
  have regular : ¬ C.IsVertex (C.edgePoint bank.val y) :=
    C.bankParameterFromEnd_nonvertex bank (C.boundaryEndEquiv retain q).2 t positive small
  have coordinates : E.pieceProjection fine.val.face.val x.val =
      E.originalBankEndProjection p := by
    obtain ⟨⟨bank, side⟩, rfl⟩ := (D.boundaryEndEquiv kept).symm.surjective p
    rcases bank with ⟨⟨face, edge⟩, boundary⟩
    cases side <;> fin_cases edge <;> rfl
  have projected : E.pieceProjection fine.val.face.val x.val =
      K.projectFace bank.val.face y.val := coordinates.trans position
  have at_point := E.originalMetricEquiv_bank_point retain fine bank parent x y projected
  rw [← D.boundaryEnd_vertexPoint_eq_endpoint p] at at_point
  exact E.original_projected_fan_at_bank_interior retain bank y regular
    (D.boundaryEndVertex kept p) at_point

end Unfoldings.ConvexRoof.CompletionMesh
