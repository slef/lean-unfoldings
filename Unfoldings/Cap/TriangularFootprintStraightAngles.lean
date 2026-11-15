module

public import Unfoldings.Cap.TriangularFootprintAngles
public import Unfoldings.Geometry.TriangleStraightBoundary

/-! Subdivision vertices inside the straight sides of a triangular footprint have angle pi. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- The projected boundary fan away from the three actual triangle corners is straight. -/
theorem projectedTotalAngle_eq_pi_of_triangle_boundary
    (T : Triangle) (domain : K.footprint = T.carrier) (w : C.Vertex Set.univ)
    (on_boundary : K.projectedVertex w ∈ frontier T.carrier)
    (noncorner : ¬ T.IsVertex (K.projectedVertex w)) :
    K.projectedTotalAngle Set.univ w = Real.pi := by
  have boundary : C.IsBoundaryVertex Set.univ w :=
    (K.projectedVertex_mem_frontier_iff w).mp (domain.symm ▸ on_boundary)
  obtain ⟨n, chain, start, finish, covers⟩ := C.exists_interval_link Set.univ w boundary
  let x := Cap.horizontal (K.folding.germFarPoint chain.first.val)
  let y := Cap.horizontal (K.folding.germFarPoint (C.linkTurn Set.univ w chain.last).val)
  have first_ray : x - K.projectedVertex w = K.projectedGermRay chain.first := rfl
  have last_ray : y - K.projectedVertex w =
      K.projectedGermRay (C.linkTurn Set.univ w chain.last) := rfl
  have first_boundary : segment ℝ (K.projectedVertex w) x ⊆ frontier T.carrier := by
    rw [← domain]
    exact K.boundary_germ_segment_frontier chain.first
      ((C.linkMate_eq_self_iff Set.univ w chain.first).mp start)
  have last_boundary : segment ℝ (K.projectedVertex w) y ⊆ frontier T.carrier := by
    rw [← domain]
    exact K.boundary_germ_segment_frontier (C.linkTurn Set.univ w chain.last)
      ((C.linkMate_eq_self_iff Set.univ w (C.linkTurn Set.univ w chain.last)).mp finish)
  have positive : 0 < K.projectedTotalAngle Set.univ w := by
    have bound := (K.projectedLinkFan chain).totalAngle_pos
    rwa [K.projectedLinkFan_totalAngle chain covers] at bound
  have endpoint := K.projected_boundary_angle_eq_endpoint chain start covers
  have different : InnerProductGeometry.angle (x - K.projectedVertex w)
      (y - K.projectedVertex w) ≠ 0 := by
    rw [first_ray, last_ray, ← endpoint]
    exact positive.ne'
  have same := T.angle_boundary_rays_eq_pi noncorner first_boundary last_boundary
    (sub_ne_zero.mp (first_ray ▸ K.projectedGermRay_ne_zero chain.first))
    (sub_ne_zero.mp (last_ray ▸ K.projectedGermRay_ne_zero (C.linkTurn Set.univ w chain.last)))
    different
  rw [first_ray, last_ray] at same
  exact endpoint.trans same

end Unfoldings.ConvexCap
