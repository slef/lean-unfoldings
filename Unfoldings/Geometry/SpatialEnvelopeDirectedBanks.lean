module

public import Unfoldings.Geometry.SpatialEnvelopePairings
public import Unfoldings.Complex.DirectedBoundaryPathGeometry
public import Unfoldings.Complex.BoundaryContourPaths

/-! Original directed banks project onto whole fine edges, preserving nonvertex points. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : Triangulation family Z)

local instance directedBankProjectionIndexFintype : Fintype T.Index :=
  @Fintype.ofFinite _ T.finite

/-- A supporting-plane projection preserves the actual three triangle corners. -/
theorem project_isVertex_iff (f : T.Index) (x : Plane) :
    (T.projectedTriangle f).IsVertex ((family (T.support f)).project x) ↔
      (T.triangle f).IsVertex x := by
  constructor
  · rintro ⟨i, same⟩
    refine ⟨i, ?_⟩
    change (family (T.support f)).project.symm ((T.projectedTriangle f).vertex i) = x
    rw [same, (family (T.support f)).project.symm_apply_apply]
  · rintro ⟨i, rfl⟩
    exact ⟨i, ((family (T.support f)).project.apply_symm_apply _).symm⟩

variable {retain : Set T.pairedComplex.Seam}

/-- The projected point of an original directed bank lies on its entire original fine edge. -/
theorem horizontal_directedBoundaryPath_mem_edge
    (p : T.pairedComplex.BoundaryEnd retain) (t : unitInterval) :
    Cap.horizontal (T.pairedFolding.toSpace retain (T.pairedComplex.directedBoundaryPath p t)) ∈
      (T.projectedTriangle (T.pairedComplex.boundaryEndEquiv retain p).1.val.face).edge
        (T.pairedComplex.boundaryEndEquiv retain p).1.val.edge := by
  let bank := (T.pairedComplex.boundaryEndEquiv retain p).1
  let q := T.pairedComplex.bankParameterFromEnd bank
    (T.pairedComplex.boundaryEndEquiv retain p).2 t
  change Cap.horizontal ((family (T.support bank.val.face)).place q.val) ∈ _
  rw [(family (T.support bank.val.face)).horizontal_place]
  exact (T.edgeProjection bank.val.face bank.val.edge q).property

/-- Projection along an original bank is injective, including its endpoints. -/
theorem horizontal_directedBoundaryPath_injective
    (p : T.pairedComplex.BoundaryEnd retain) :
    Function.Injective (fun t : unitInterval => Cap.horizontal
      (T.pairedFolding.toSpace retain (T.pairedComplex.directedBoundaryPath p t))) := by
  let bank := (T.pairedComplex.boundaryEndEquiv retain p).1
  let side := (T.pairedComplex.boundaryEndEquiv retain p).2
  have different : ((T.triangle bank.val.face).endpoint bank.val.edge side).val ≠
      ((T.triangle bank.val.face).endpoint bank.val.edge (!side)).val := by
    cases side
    · exact (T.triangle bank.val.face).edge_endpoints_ne bank.val.edge
    · exact ((T.triangle bank.val.face).edge_endpoints_ne bank.val.edge).symm
  intro s t same
  change Cap.horizontal ((family (T.support bank.val.face)).place _) =
    Cap.horizontal ((family (T.support bank.val.face)).place _) at same
  rw [(family (T.support bank.val.face)).horizontal_place,
    (family (T.support bank.val.face)).horizontal_place] at same
  have physical := (family (T.support bank.val.face)).project.injective same
  exact Subtype.ext ((AffineMap.lineMap_injective ℝ different) physical)

/-- The actual projected endpoints of a fine bank are distinct. -/
theorem horizontal_boundaryPosition_ne (p : T.pairedComplex.BoundaryEnd retain) :
    Cap.horizontal (T.pairedFolding.boundaryPosition p) ≠
      Cap.horizontal
        (T.pairedFolding.boundaryPosition (T.pairedComplex.boundaryTurn retain p)) := by
  intro same
  have equal : (0 : unitInterval) = 1 := T.horizontal_directedBoundaryPath_injective p (by
    dsimp only
    rw [T.pairedFolding.horizontal_directedBoundaryPath,
      T.pairedFolding.horizontal_directedBoundaryPath]
    change AffineMap.lineMap _ _ (0 : ℝ) = AffineMap.lineMap _ _ (1 : ℝ)
    simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using same)
  exact zero_ne_one equal

/-- Intrinsic nonvertex copies remain nonvertices in the original projected bank triangle. -/
theorem horizontal_directedBoundaryPath_nonvertex
    (p : T.pairedComplex.BoundaryEnd retain) (t : unitInterval)
    (regular : ∀ v : T.pairedComplex.Vertex retain,
      T.pairedComplex.directedBoundaryPath p t ≠ T.pairedComplex.vertexPoint retain v) :
    ¬ (T.projectedTriangle (T.pairedComplex.boundaryEndEquiv retain p).1.val.face).IsVertex
      (Cap.horizontal (T.pairedFolding.toSpace retain
        (T.pairedComplex.directedBoundaryPath p t))) := by
  let bank := (T.pairedComplex.boundaryEndEquiv retain p).1
  let q := T.pairedComplex.bankParameterFromEnd bank
    (T.pairedComplex.boundaryEndEquiv retain p).2 t
  change ¬ (T.projectedTriangle bank.val.face).IsVertex
    (Cap.horizontal ((family (T.support bank.val.face)).place q.val))
  rw [(family (T.support bank.val.face)).horizontal_place, T.project_isVertex_iff]
  intro vertex
  obtain ⟨v, equal⟩ := (T.pairedComplex.mem_range_vertexPoint_iff retain
    (T.pairedComplex.edgePoint bank q)).mpr vertex
  exact regular v equal.symm

end Unfoldings.SpatialEnvelope.Triangulation
