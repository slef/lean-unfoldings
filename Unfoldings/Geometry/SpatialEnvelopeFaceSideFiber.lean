module

public import Unfoldings.Geometry.SpatialEnvelopeFaceSideCellAgreement
public import Unfoldings.Geometry.SpatialEnvelopeHalfspaceChart
public import Unfoldings.Geometry.SpatialEnvelopeIncidentSupport

/-! Every original copy over a two-plane germ belongs to one named side. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

/-- With both halfplane germs identified, their canonical region maps
exhaust the entire original cut fiber. -/
theorem exists_faceSideRegionMap_of_local_heights
    (f : Plane →ᵃ[ℝ] ℝ) (proper : f ≠ 0) (signs : A → Bool)
    (aligned : ∀ c z, z ∈ P.footprint c → 0 ≤ AffineArrangement.signed f (signs c) z)
    (cuts : Set Plane) (closed : IsClosed cuts) (level : ∀ z ∈ cuts, f z = 0)
    (anchor : Bool → A) (sides : ∀ side, signs (anchor side) = side)
    {p : Plane} (source : ∀ side : Bool, PolygonalPoint
      ((family (P.support (anchor side))).project.symm '' P.faceSideRegion (anchor side) f signs))
    (source_at : ∀ side, (family (P.support (anchor side))).project (source side).val = p)
    (germs : ∀ side : Bool, ∃ δ > 0, ∀ z, dist z p < δ →
      0 ≤ AffineArrangement.signed f side z →
        height family z = (family (P.support (anchor side))).height z)
    (x : P.Cut cuts) (position : Cap.horizontal (P.restoreCut cuts x).val = p) :
    ∃ side, x = P.faceSideRegionMap (anchor side) f proper signs aligned cuts closed level
      (source side) := by
  obtain ⟨⟨a, y⟩, represent⟩ := MetricGluing.point_surjective (fun a => P.spatialCell a)
    (P.cutPhysicalSeams cuts).relation (P.cutIsometryEquiv cuts x)
  have physical : y.val = (P.restoreCut cuts x).val :=
    (congrArg (P.cutPhysicalSeams cuts).fold represent).trans (P.fold_cutIsometryEquiv cuts x)
  have member : p ∈ P.footprint a := by
    rw [← position, ← physical]
    exact P.horizontal_mem_footprint_of_spatial a y
  let side := signs a
  obtain ⟨ε, εpos, germ⟩ := germs side
  have same : (family (P.support a)).height = (family (P.support (anchor side))).height :=
    P.incident_support_eq_of_side_germ (anchor side) a f signs aligned member
      (sides side).symm Metric.isOpen_ball (Metric.mem_ball_self εpos)
      (fun z near side_mem => germ z near (by rwa [sides side] at side_mem))
  let copy : P.FaceSideIndex (anchor side) signs := ⟨a, same, (sides side).symm⟩
  have graph : (P.restoreCut cuts x).val = point family p := by
    obtain ⟨q, rfl_q⟩ := (P.restoreCut cuts x).property
    have q_eq : q = p := (horizontal_point family q).symm.trans
      ((congrArg Cap.horizontal rfl_q).trans position)
    exact rfl_q.symm.trans (congrArg (point family) q_eq)
  have source_support := ((P.mem_faceSidePlanarRegion_iff (anchor side) f signs
    (source side).val).mp (source side).property).1
  rw [source_at] at source_support
  have place : y.val = (family (P.support (anchor side))).place (source side).val := by
    rw [physical, graph, point_eq_place family (P.support (anchor side)) source_support,
      ← source_at side, (family (P.support (anchor side))).project.symm_apply_apply]
  refine ⟨side, (P.cutIsometryEquiv cuts).injective ?_⟩
  exact represent.symm.trans (P.faceSideRegionMap_eq_of_spatial_copy (anchor side) f proper
    signs aligned cuts closed level copy y (source side) place).symm

end Unfoldings.SpatialEnvelope.WholePartition
