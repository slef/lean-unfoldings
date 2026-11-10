module

public import Unfoldings.Cap.Basic
public import Mathlib.Analysis.Convex.GaugeRescale

/-! Convex cap disk topology is derived from its actual injective planar projection. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem compact_footprint : IsCompact K.footprint :=
  K.folding.compact_surface.image Cap.horizontalCLM.continuous

theorem exists_footprintDisk : Nonempty (K.footprint ≃ₜ Metric.closedBall (0 : Plane) 1) := by
  obtain ⟨h, _interior, closed, _boundary⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall K.convex_projection
      K.interior_projection K.compact_footprint.isBounded
  change h '' closure K.footprint = Metric.closedBall (0 : Plane) 1 at closed
  rw [K.compact_footprint.isClosed.closure_eq] at closed
  exact ⟨(h.image K.footprint).trans (Homeomorph.setCongr closed)⟩

/-- No disk certificate is assumed in the cap input. -/
def diskHomeomorph : C.Realization Set.univ ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  K.footprintHomeomorph.trans (Classical.choice K.exists_footprintDisk)

end Unfoldings.ConvexCap
