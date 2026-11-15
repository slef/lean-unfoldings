module

public import Unfoldings.Cap.RimAngles
public import Unfoldings.Geometry.TriangleBoundaryRays

/-! An actual triangular cap footprint fixes its three projected corner fan angles exactly. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- A physical fan over a triangular footprint corner has precisely that projected angle. -/
theorem projectedTotalAngle_eq_triangle_corner (T : Triangle) (domain : K.footprint = T.carrier)
    (w : C.Vertex Set.univ) (i : Fin 3) (apex : K.projectedVertex w = T.vertex i) :
    K.projectedTotalAngle Set.univ w = T.cornerAngle i := by
  have boundary : C.IsBoundaryVertex Set.univ w := by
    apply (K.projectedVertex_mem_frontier_iff w).mp
    rw [domain, apex]
    exact T.edge_subset_frontier i (left_mem_segment ℝ _ _)
  obtain ⟨n, chain, start, finish, covers⟩ := C.exists_interval_link Set.univ w boundary
  let x := Cap.horizontal (K.folding.germFarPoint chain.first.val)
  let y := Cap.horizontal (K.folding.germFarPoint (C.linkTurn Set.univ w chain.last).val)
  have first_ray : x - T.vertex i = K.projectedGermRay chain.first := by
    rw [← apex]
    rfl
  have last_ray : y - T.vertex i =
      K.projectedGermRay (C.linkTurn Set.univ w chain.last) := by
    rw [← apex]
    rfl
  have first_boundary : segment ℝ (T.vertex i) x ⊆ frontier T.carrier := by
    have segment_boundary := K.boundary_germ_segment_frontier chain.first
      ((C.linkMate_eq_self_iff Set.univ w chain.first).mp start)
    rwa [domain, apex] at segment_boundary
  have last_boundary : segment ℝ (T.vertex i) y ⊆ frontier T.carrier := by
    have segment_boundary := K.boundary_germ_segment_frontier
      (C.linkTurn Set.univ w chain.last)
      ((C.linkMate_eq_self_iff Set.univ w (C.linkTurn Set.univ w chain.last)).mp finish)
    rwa [domain, apex] at segment_boundary
  have positive : 0 < K.projectedTotalAngle Set.univ w := by
    have bound := (K.projectedLinkFan chain).totalAngle_pos
    rwa [K.projectedLinkFan_totalAngle chain covers] at bound
  have endpoint := K.projected_boundary_angle_eq_endpoint chain start covers
  have different : InnerProductGeometry.angle (x - T.vertex i) (y - T.vertex i) ≠ 0 := by
    rw [first_ray, last_ray, ← endpoint]
    exact positive.ne'
  have same := T.angle_boundary_rays_eq_cornerAngle i first_boundary last_boundary
    (sub_ne_zero.mp (first_ray ▸ K.projectedGermRay_ne_zero chain.first))
    (sub_ne_zero.mp (last_ray ▸ K.projectedGermRay_ne_zero (C.linkTurn Set.univ w chain.last)))
    different
  rw [first_ray, last_ray] at same
  exact endpoint.trans same

end Unfoldings.ConvexCap
