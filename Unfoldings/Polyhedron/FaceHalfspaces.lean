module

public import Unfoldings.Polyhedron.SupportingNormals
public import Unfoldings.Topology.PathFrontier
public import Mathlib.Analysis.Convex.Segment

/-! The original supporting face planes describe exactly the entire convex body. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P in
/-- No extra halfspaces or facet-maximality hypotheses are needed, even with coplanar
subdivisions: the original triangular face supports cut out precisely the original hull. -/
theorem vertexHull_eq_face_halfspaces :
    F.vertexHull = {z | ∀ f, inner ℝ (N.normal f) (z - F.place f 0) ≤ 0} := by
  ext z
  constructor
  · exact fun member f => N.supporting f z member
  · intro supported
    by_contra outside
    obtain ⟨c, inside⟩ := P.interior_nonempty
    let path : unitInterval → Space := fun t => AffineMap.lineMap c z (t : ℝ)
    have continuous : Continuous path := by
      dsimp only [path]
      fun_prop
    obtain ⟨t, positive, before, boundary⟩ := exists_inner_time_mem_frontier
      F.compact_vertexHull.isClosed path continuous
      (by simpa only [path, Set.Icc.coe_zero, AffineMap.lineMap_apply_zero] using inside)
      (by simpa only [path, Set.Icc.coe_one, AffineMap.lineMap_apply_one] using outside)
    rw [← P.boundary] at boundary
    obtain ⟨f, x, hx, at_point⟩ := Set.mem_iUnion.mp boundary
    have zero : inner ℝ (N.normal f) (path t - F.place f 0) = 0 := by
      rw [← at_point]
      exact N.on_plane f x
    have strict := N.supporting_strict f inside
    have nonpositive := supported f
    have combination : inner ℝ (N.normal f) (path t - F.place f 0) =
        (1 - (t : ℝ)) * inner ℝ (N.normal f) (c - F.place f 0) +
          (t : ℝ) * inner ℝ (N.normal f) (z - F.place f 0) := by
      simp only [path, AffineMap.lineMap_apply_module', inner_sub_right, inner_add_right,
        real_inner_smul_right]
      ring
    have first_negative := mul_neg_of_pos_of_neg (sub_pos.mpr before) strict
    have last_nonpositive := mul_nonpos_of_nonneg_of_nonpos positive.le nonpositive
    linarith [combination]

end Unfoldings.SpatialFolding.ConvexBoundary
