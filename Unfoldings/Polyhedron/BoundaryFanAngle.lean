module

public import Unfoldings.Polyhedron.IntervalLink
public import Unfoldings.Polyhedron.BoundaryDirections
public import Unfoldings.Polyhedron.LinkFanTurn
public import Unfoldings.Complex.RestoredLinkChain

/-! The actual two boundary directions bound the complete intrinsic one-sided fan angle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) {retain : Set C.Seam}

/-- The two actual boundary germs, with no supplied link order, bound the full fan angle. -/
theorem boundary_endpoint_angle_le_totalAngle (p : C.BoundaryEnd retain) :
    InnerProductGeometry.angle (F.germDirection p.val)
      (F.germDirection (C.boundaryMate retain p).val) ≤
        C.totalAngle retain (C.boundaryEndVertex retain p) := by
  obtain ⟨n, chain, first, last, covers⟩ := C.exists_boundary_link retain p
  have bound := F.intervalLink_endpoint_angle_le chain covers
  rw [first, last] at bound
  exact bound

/-- A cut boundary's actual one-sided turn is bounded by its spatial bend at every
interior original vertex with nonnegative curvature. All cut-copy fan data is derived. -/
theorem abs_boundary_turn_le_spatial_bend (p : C.BoundaryEnd retain)
    (internal : ¬ C.IsBoundaryVertex Set.univ
      (C.vertexForgetCuts (Set.subset_univ retain) (C.boundaryEndVertex retain p)))
    (convex : C.totalAngle Set.univ
      (C.vertexForgetCuts (Set.subset_univ retain) (C.boundaryEndVertex retain p)) ≤
        2 * Real.pi) :
    |Real.pi - C.totalAngle retain (C.boundaryEndVertex retain p)| ≤
      InnerProductGeometry.angle (-F.germDirection p.val)
        (F.germDirection (C.boundaryMate retain p).val) := by
  obtain ⟨n, chain, first, last, covers⟩ := C.exists_boundary_link retain p
  let restored := C.restoreLinkChain (Set.subset_univ retain) chain
  have sum : (∑ i : Fin (n + 1),
      (C.triangle (restored.point i).val.1.1).cornerAngle (restored.point i).val.1.2) =
        C.totalAngle retain (C.boundaryEndVertex retain p) :=
    C.sum_linkCornerAngle retain _ chain covers
  have first_ray : F.germDirection restored.first.val = F.germDirection p.val :=
    congrArg F.germDirection first
  have last_ray : F.germDirection (C.linkTurn Set.univ _ restored.last).val =
      F.germDirection (C.boundaryMate retain p).val := congrArg F.germDirection last
  have bound := F.abs_link_exterior_turn_le_spatial_bend restored internal convex
  rwa [sum, first_ray, last_ray] at bound

end Unfoldings.SpatialFolding
