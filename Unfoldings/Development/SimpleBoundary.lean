module

public import Unfoldings.Development.BoundaryDisplacements
public import Unfoldings.Complex.DiskCuts
public import Unfoldings.Complex.BoundaryContour

/-! The boundary of an injectively developed intrinsic disk is a finite simple polygon. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

/-- Each actual unpaired closed bank develops to exactly its endpoint segment. -/
theorem image_bankMap_eq_segment (bank : C.BoundaryBank retain) :
    D.toPlane '' Set.range (C.bankMap retain bank) =
      segment ℝ (D.toPlane (C.vertexPoint retain ((C.boundaryGraph retain).left bank).val))
        (D.toPlane (C.vertexPoint retain ((C.boundaryGraph retain).right bank).val)) := by
  change D.toPlane '' Set.range (C.bankMap retain bank) =
    segment ℝ (D.place bank.val.face ((C.triangle bank.val.face).vertex bank.val.edge))
      (D.place bank.val.face ((C.triangle bank.val.face).vertex (Triangle.next bank.val.edge)))
  have image : (D.place bank.val.face).toAffineMap ''
      segment ℝ ((C.triangle bank.val.face).vertex bank.val.edge)
        ((C.triangle bank.val.face).vertex (Triangle.next bank.val.edge)) =
      segment ℝ (D.place bank.val.face ((C.triangle bank.val.face).vertex bank.val.edge))
        (D.place bank.val.face ((C.triangle bank.val.face).vertex
          (Triangle.next bank.val.edge))) := image_segment ℝ _ _ _
  rw [← image]
  ext z
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x.val, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨C.bankMap retain bank ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩

/-- The entire bank boundary, retaining each original bank label, is a finite union of segments. -/
theorem image_boundary_eq_bank_segments :
    D.toPlane '' C.bankBoundary retain =
      ⋃ bank : C.BoundaryBank retain,
        segment ℝ (D.toPlane (C.vertexPoint retain ((C.boundaryGraph retain).left bank).val))
          (D.toPlane (C.vertexPoint retain ((C.boundaryGraph retain).right bank).val)) := by
  rw [TriangleComplex.bankBoundary, Set.image_iUnion]
  congr 1
  funext bank
  exact D.image_bankMap_eq_segment bank

/-- Injectivity on the closed disk gives a Jordan curve on its actual bank boundary. -/
theorem image_boundary_isJordanCurve (F : SpatialFolding C)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    (injective : Function.Injective D.toPlane) :
    Schoenflies.IsJordanCurve (D.toPlane '' C.bankBoundary retain) := by
  let contour := C.boundaryContourOfConnected retain
    (F.boundaryGraph_connected_of_disk retain disk)
  let f : C(C.Realization retain, Plane) := ⟨D.toPlane, D.toPlane_lipschitz.continuous⟩
  have jordan := ((C.boundaryGraph retain).mapEmbedding f injective).cycle_isJordanCurve
    (fun edge => injective.comp (F.boundaryGraph_edge_injective retain edge))
    (C.boundaryCycle_isCycleThrough retain contour.cycle contour.closes)
  rw [C.boundaryCycle_edgesCover_eq retain contour.cycle contour.covers f injective] at jordan
  exact jordan

/-- This polygon is the exact frontier of the developed footprint. -/
theorem frontier_range_eq_image_boundary (F : SpatialFolding C)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    (injective : Function.Injective D.toPlane) :
    frontier (Set.range D.toPlane) = D.toPlane '' C.bankBoundary retain := by
  obtain ⟨i, embedding⟩ := F.exists_cutComplementOpenEmbedding_of_disk
    (show retain ⊆ retain from fun _ h => h) disk
  exact Unfoldings.frontier_range_eq_boundaryImage (F.exists_bankBoundaryChart retain)
    i embedding ⟨D.toPlane, D.toPlane_lipschitz.continuous⟩ injective

/-- A closed-disk embedding has an actual simple polygon as its footprint frontier. -/
theorem frontier_is_simple_polygon (F : SpatialFolding C)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    (injective : Function.Injective D.toPlane) :
    Schoenflies.IsJordanCurve (frontier (Set.range D.toPlane)) ∧
      frontier (Set.range D.toPlane) =
        ⋃ bank : C.BoundaryBank retain,
          segment ℝ (D.toPlane (C.vertexPoint retain ((C.boundaryGraph retain).left bank).val))
            (D.toPlane (C.vertexPoint retain ((C.boundaryGraph retain).right bank).val)) := by
  rw [D.frontier_range_eq_image_boundary F disk injective]
  exact ⟨D.image_boundary_isJordanCurve F disk injective, D.image_boundary_eq_bank_segments⟩

end Unfoldings.FacewiseDevelopment
