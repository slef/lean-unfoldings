module

public import Unfoldings.Roof.Topology
public import Unfoldings.Roof.VertexProgress
public import Unfoldings.Complex.IntrinsicBoundary
public import Unfoldings.Complex.RelativeSeamGeometry

/-!
# The actual cap rim and the projected footprint boundary

Intrinsic boundary preservation for disks identifies the unpaired triangle
banks with the frontier of the convex footprint. Thus an internal projected
vertex is exactly an original nonboundary vertex, rather than an extra input
condition on the forest construction.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem projected_mem_frontier_iff_bankBoundary (x : C.Realization Set.univ) :
    Cap.horizontal (K.folding.toSpace Set.univ x) ∈ frontier K.footprint ↔
      x ∈ C.bankBoundary Set.univ := by
  obtain ⟨h, _, closed, boundary⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall K.convex_projection
      K.interior_projection K.compact_footprint.isBounded
  change h '' frontier K.footprint = Metric.sphere (0 : Plane) 1 at boundary
  change h '' closure K.footprint = Metric.closedBall (0 : Plane) 1 at closed
  rw [K.compact_footprint.isClosed.closure_eq] at closed
  let d : C.Realization Set.univ ≃ₜ Metric.closedBall (0 : Plane) 1 :=
    K.footprintHomeomorph.trans ((h.image K.footprint).trans (Homeomorph.setCongr closed))
  have norm_iff (p : Plane) : p ∈ frontier K.footprint ↔ ‖h p‖ = 1 := by
    have image : p ∈ frontier K.footprint ↔ h p ∈ h '' frontier K.footprint := by
      constructor
      · intro present
        exact ⟨p, present, rfl⟩
      · rintro ⟨q, present, equal⟩
        exact h.injective equal ▸ present
    rw [image, boundary]
    simp only [Metric.mem_sphere, dist_zero_right]
  rw [norm_iff, K.folding.bankBoundary_iff_disk_norm_eq_one Set.univ d x]
  rfl

theorem projected_mem_interior_iff_not_bankBoundary (x : C.Realization Set.univ) :
    Cap.horizontal (K.folding.toSpace Set.univ x) ∈ interior K.footprint ↔
      x ∉ C.bankBoundary Set.univ := by
  have frontier := K.projected_mem_frontier_iff_bankBoundary x
  have not_interior := mem_frontier_iff_notMem_interior (K.toFootprint x).property
  constructor
  · intro inside boundary
    exact (not_interior.mp (frontier.mpr boundary)) inside
  · intro outside
    by_contra not_inside
    exact outside (frontier.mp (not_interior.mpr not_inside))

theorem projectedVertex_mem_frontier_iff (v : C.Vertex Set.univ) :
    K.projectedVertex v ∈ frontier K.footprint ↔ C.IsBoundaryVertex Set.univ v := by
  rw [projectedVertex, K.projected_mem_frontier_iff_bankBoundary,
    C.vertexPoint_mem_bankBoundary_iff]

theorem projectedVertex_mem_interior_iff (v : C.Vertex Set.univ) :
    K.projectedVertex v ∈ interior K.footprint ↔ ¬ C.IsBoundaryVertex Set.univ v := by
  rw [projectedVertex, K.projected_mem_interior_iff_not_bankBoundary,
    C.vertexPoint_mem_bankBoundary_iff]

end Unfoldings.ConvexRoof
