module

public import Unfoldings.Cap.ProjectedFanOrientation
public import Unfoldings.Geometry.PositiveRayCones

/-! Positive physical bank rays identify original germs independently of edge lengths. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {w : C.Vertex Set.univ}

/-- Even differently scaled outgoing projected vectors identify the same original germ
when both occupied original face sides are positive. -/
theorem projected_positive_germ_unique_of_positive_scale (p q : C.LinkGerm Set.univ w)
    (positive_p : 0 < K.projectedGermOrientation p.val)
    (positive_q : 0 < K.projectedGermOrientation q.val) {r : ℝ} (positive : 0 < r)
    (ray : K.projectedGermRay p = r • K.projectedGermRay q) : p = q := by
  have left : 0 < orient 0 (r • K.projectedGermRay q)
      (K.projectedGermRay (C.linkTurn Set.univ w p)) := by
    rw [← ray, K.projectedGermRay_orient]
    exact positive_p
  have right : 0 < orient 0 (K.projectedGermRay q)
      (K.projectedGermRay (C.linkTurn Set.univ w q)) := by
    rw [K.projectedGermRay_orient]
    exact positive_q
  have face : p.val.1.1 = q.val.1.1 := by
    by_contra different
    have separated : Disjoint
        (strictRayCone (K.projectedGermRay p)
          (K.projectedGermRay (C.linkTurn Set.univ w p)))
        (strictRayCone (K.projectedGermRay q)
          (K.projectedGermRay (C.linkTurn Set.univ w q))) := by
      rw [K.projectedGermRay_cone, K.projectedGermRay_cone]
      exact (K.projectedTriangle _).disjoint_cornerDirections (K.projectedTriangle _)
        p.val.1.2 q.val.1.2
        ((K.projectedGerm_apex p).trans (K.projectedGerm_apex q).symm)
        (K.projectedTriangles_nonoverlapping different)
    rw [ray] at separated
    exact not_disjoint_strictRayCones_of_positive_scaled_ray positive left right separated
  have corner : p.val.1 = q.val.1 := congrArg Subtype.val
    (K.cornerAt_face_injective w (a₁ := ⟨p.val.1, p.property⟩)
      (a₂ := ⟨q.val.1, q.property⟩) face)
  apply Subtype.ext
  apply Prod.ext corner
  by_contra sides
  have turned : C.turnGerm p.val = q.val := by
    change (p.val.1, !p.val.2) = q.val
    refine Prod.ext (by exact corner) ?_
    cases hp : p.val.2 <;> cases hq : q.val.2 <;> simp_all
  rw [← turned, K.projectedGermOrientation_turn] at positive_q
  linarith

end Unfoldings.ConvexCap
