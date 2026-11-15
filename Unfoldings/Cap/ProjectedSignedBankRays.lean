module

public import Unfoldings.Cap.ProjectedRawBankRays

/-! Physical ray uniqueness on either occupied side, independently of bank length. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {w : C.Vertex Set.univ}

/-- Equal directed rays with the same occupied side identify the original germ,
including negative orientations and different vector lengths. -/
theorem projected_germ_unique_of_same_orientation_positive_scale
    (p q : C.LinkGerm Set.univ w)
    (sign : 0 < K.projectedGermOrientation p.val * K.projectedGermOrientation q.val)
    {r : ℝ} (positive : 0 < r) (ray : K.projectedGermRay p = r • K.projectedGermRay q) :
    p = q := by
  have product : 0 <
      orient 0 (K.projectedGermRay p) (K.projectedGermRay (C.linkTurn Set.univ w p)) *
        orient 0 (K.projectedGermRay q) (K.projectedGermRay (C.linkTurn Set.univ w q)) := by
    simpa only [K.projectedGermRay_orient] using sign
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
    rw [ray, strictRayCone_smul_left positive] at separated
    have area : orient 0 (r • K.projectedGermRay q)
        (K.projectedGermRay (C.linkTurn Set.univ w p)) =
      r * orient 0 (K.projectedGermRay q) (K.projectedGermRay (C.linkTurn Set.univ w p)) := by
      simp only [orient, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, sub_zero]
      ring
    rw [ray, area, mul_assoc] at product
    exact not_disjoint_strictRayCones_of_same_initial_ray
      ((mul_pos_iff_of_pos_left positive).mp product) separated
  have corner : p.val.1 = q.val.1 := congrArg Subtype.val
    (K.cornerAt_face_injective w (a₁ := ⟨p.val.1, p.property⟩)
      (a₂ := ⟨q.val.1, q.property⟩) face)
  apply Subtype.ext
  apply Prod.ext corner
  by_contra sides
  have turned : C.turnGerm p.val = q.val := by
    change (p.val.1, !p.val.2) = q.val
    refine Prod.ext corner ?_
    cases hp : p.val.2 <;> cases hq : q.val.2 <;> simp_all
  rw [← turned, K.projectedGermOrientation_turn] at sign
  nlinarith [sq_nonneg (K.projectedGermOrientation p.val)]

/-- Original apex, positive ray scale and occupied-side sign suffice in either orientation. -/
theorem projected_raw_germ_unique_of_same_orientation_positive_scale (p q : C.Germ)
    (apex : (K.projectedTriangle p.1.1).vertex p.1.2 =
      (K.projectedTriangle q.1.1).vertex q.1.2)
    (sign : 0 < K.projectedGermOrientation p * K.projectedGermOrientation q)
    {r : ℝ} (positive : 0 < r)
    (direction : Cap.horizontal (K.folding.germDirection p) =
      r • Cap.horizontal (K.folding.germDirection q)) : p = q := by
  let vertex := C.vertexOfCorner Set.univ p.1
  let first : C.LinkGerm Set.univ vertex := ⟨p, rfl⟩
  have at_last : C.vertexOfCorner Set.univ q.1 = vertex :=
    K.projectedVertex_injective apex.symm
  let last : C.LinkGerm Set.univ vertex := ⟨q, at_last⟩
  have rays : K.projectedGermRay first = r • K.projectedGermRay last := by
    rw [← K.horizontal_germDirection first, ← K.horizontal_germDirection last]
    exact direction
  exact congrArg (fun g : C.LinkGerm Set.univ vertex => g.val)
    (K.projected_germ_unique_of_same_orientation_positive_scale first last sign positive rays)

end Unfoldings.ConvexCap
