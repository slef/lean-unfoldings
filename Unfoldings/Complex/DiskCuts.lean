module

public import Unfoldings.Complex.DiskBoundaryQuotient
public import Unfoldings.Complex.BoundaryAtlas
public import Unfoldings.Complex.BoundaryCycleCarrier
public import Unfoldings.Topology.DiskSubsetChart
public import Unfoldings.Topology.DiskFromBoundary

/-!
# Disk cuts are disks exactly when their actual bank graph is connected

The original disk may already have banks. Further cuts always admit a planar
embedding, including when they disconnect the surface. A connected bank graph
then gives one Jordan boundary, from which the actual disk homeomorphism is
constructed. No nonoverlap of a development is assumed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

include F

theorem bankBoundary_connected_of_disk (retain : Set C.Seam)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1) :
    IsConnected (C.bankBoundary retain) := by
  let := plane_unit_sphere_connected
  let f : Metric.sphere (0 : Plane) 1 → C.Realization retain :=
    disk.symm ∘ unitSphereDiskInclusion
  have images : Set.range f = C.bankBoundary retain := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      apply (F.bankBoundary_iff_disk_norm_eq_one retain disk _).mpr
      simp only [f, Function.comp_apply, disk.apply_symm_apply]
      exact mem_sphere_zero_iff_norm.mp z.property
    · intro boundary
      let z : Metric.sphere (0 : Plane) 1 :=
        ⟨(disk x).val, mem_sphere_zero_iff_norm.mpr
          ((F.bankBoundary_iff_disk_norm_eq_one retain disk x).mp boundary)⟩
      exact ⟨z, disk.symm_apply_apply x⟩
  rw [← images]
  exact isConnected_range (disk.symm.continuous.comp unitSphereDiskInclusion.continuous)

theorem boundaryGraph_connected_of_disk (retain : Set C.Seam)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1) :
    (C.boundaryGraph retain).adjacencyGraph.Connected := by
  apply (C.boundaryGraph retain).connected_of_isConnected
  rw [C.boundaryGraph_carrier]
  exact F.bankBoundary_connected_of_disk retain disk

theorem exists_planarCutEmbedding_of_disk {small large : Set C.Seam}
    (inclusion : small ⊆ large)
    (disk : C.Realization large ≃ₜ Metric.closedBall (0 : Plane) 1) :
    ∃ f : C(C.Realization small, Plane), Topology.IsClosedEmbedding f := by
  obtain ⟨g, embedded, _avoids⟩ := F.exists_cutEmbedding inclusion
  let f : C(C.Realization small, Plane) :=
    ⟨fun x => (disk (g x)).val,
      continuous_subtype_val.comp (disk.continuous.comp g.continuous)⟩
  exact ⟨f, f.continuous.isClosedEmbedding
    (Subtype.val_injective.comp (disk.injective.comp embedded.injective))⟩

theorem exists_cutComplementOpenEmbedding_of_disk {small large : Set C.Seam}
    (inclusion : small ⊆ large)
    (disk : C.Realization large ≃ₜ Metric.closedBall (0 : Plane) 1) :
    ∃ i : ↥((C.bankBoundary small)ᶜ) → Plane, Topology.IsOpenEmbedding i := by
  let Q := C.forgetCutsBoundaryQuotient inclusion
  have absorbs : ∀ x, ‖(disk x).val‖ = 1 → x ∈ Q.boundaryImage := by
    intro x norm
    obtain ⟨y, rfl⟩ := C.forgetCuts_surjective inclusion x
    exact ⟨y, C.bankBoundary_preimage_forgetCuts inclusion
      ((F.bankBoundary_iff_disk_norm_eq_one large disk _).mpr norm), rfl⟩
  obtain ⟨i, embedded⟩ := exists_openEmbedding_disk_compl disk
    (Q.isClosed_boundaryImage (C.isClosed_bankBoundary small)) absorbs
  let h := Q.complementHomeomorph (C.isClosed_bankBoundary small)
  exact ⟨i ∘ h, embedded.comp h.isOpenEmbedding⟩

theorem exists_cutDisk_of_boundaryGraph_connected {small large : Set C.Seam}
    (inclusion : small ⊆ large)
    (disk : C.Realization large ≃ₜ Metric.closedBall (0 : Plane) 1)
    (connected : (C.boundaryGraph small).adjacencyGraph.Connected) :
    Nonempty (C.Realization small ≃ₜ Metric.closedBall (0 : Plane) 1) := by
  obtain ⟨v⟩ := connected.nonempty
  obtain ⟨bank, _w, _link⟩ := C.boundaryGraph_vertex_incident small v
  let p := (C.boundaryEndEquiv small).symm (bank, false)
  obtain ⟨n, cycle, _first, closes⟩ := C.exists_boundaryCycle small p
  have covers := C.boundaryCycle_covers_of_connected small cycle closes connected
  obtain ⟨f, embedded⟩ := F.exists_planarCutEmbedding_of_disk inclusion disk
  have jordan := ((C.boundaryGraph small).mapEmbedding f embedded.injective).cycle_isJordanCurve
    (fun edge => embedded.injective.comp (F.boundaryGraph_edge_injective small edge))
    (C.boundaryCycle_isCycleThrough small cycle closes)
  rw [C.boundaryCycle_edgesCover_eq small cycle covers f embedded.injective] at jordan
  obtain ⟨i, open_embedding⟩ := F.exists_cutComplementOpenEmbedding_of_disk inclusion disk
  exact exists_diskHomeomorph_of_Jordan_boundary (F.exists_bankBoundaryChart small)
    i open_embedding f embedded.injective jordan

theorem cutDisk_iff_boundaryGraph_connected {small large : Set C.Seam}
    (inclusion : small ⊆ large)
    (disk : C.Realization large ≃ₜ Metric.closedBall (0 : Plane) 1) :
    Nonempty (C.Realization small ≃ₜ Metric.closedBall (0 : Plane) 1) ↔
      (C.boundaryGraph small).adjacencyGraph.Connected := by
  constructor
  · rintro ⟨cut⟩
    exact F.boundaryGraph_connected_of_disk small cut
  · exact F.exists_cutDisk_of_boundaryGraph_connected inclusion disk

end Unfoldings.SpatialFolding
