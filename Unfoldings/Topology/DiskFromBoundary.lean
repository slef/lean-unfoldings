module

public import Unfoldings.Topology.BoundaryInvariance
public import Unfoldings.Topology.CompactJordanDisk

/-!
# A compact surface with one Jordan boundary is a disk

Actual half-plane boundary charts and an open planar model of the boundary
complement identify the frontier of any planar embedding. If that exact image
boundary is a Jordan curve, compact planar Jordan classification supplies the
disk homeomorphism. No disk presentation is an input.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

open PlanarTopology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] {B : Set X}

theorem exists_diskHomeomorph_of_Jordan_boundary
    (charts : ∀ x ∈ B, Nonempty (HalfPlaneBoundaryChart B x))
    (i : ↥(Bᶜ) → Plane) (embedding : Topology.IsOpenEmbedding i)
    (f : C(X, Plane)) (injective : Function.Injective f)
    (jordan : Schoenflies.IsJordanCurve (f '' B)) :
    Nonempty (X ≃ₜ Metric.closedBall (0 : Plane) 1) := by
  have nonempty : B.Nonempty := by
    obtain ⟨y, x, hx, _equal⟩ := jordan.nonempty
    exact ⟨x, hx⟩
  have outside := boundary_compl_nonempty_of_halfPlaneCharts nonempty charts
  have interior := interior_range_nonempty_of_open_compl i embedding f injective outside
  have boundary := frontier_range_eq_boundaryImage charts i embedding f injective
  have actual_jordan : Schoenflies.IsJordanCurve (frontier (Set.range f)) := boundary.symm ▸ jordan
  obtain ⟨disk⟩ := exists_diskHomeomorph_of_compact_Jordan_frontier
    (isCompact_range f.continuous) interior actual_jordan
  exact ⟨(f.continuous.isClosedEmbedding injective).isEmbedding.toHomeomorph.trans disk⟩

end Unfoldings
