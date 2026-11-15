module

public import Unfoldings.Cap.ProjectedInterval
public import Unfoldings.Cap.ProjectionContour

/-! Positive projected bank directions identify actual original germs. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {w : C.Vertex Set.univ}

/-- The projected link determinant is the physical signed corner area. -/
theorem projectedGermRay_orient (p : C.LinkGerm Set.univ w) :
    orient 0 (K.projectedGermRay p)
      (K.projectedGermRay (C.linkTurn Set.univ w p)) = K.projectedGermOrientation p.val := by
  have apex := K.projectedGerm_apex p
  unfold projectedGermRay
  rw [← apex]
  change orient 0 (_ - _) (_ - _) = orient _ _ _
  simp only [projectedTriangle, Triangle.affineImage_vertex, projectFace,
    SpatialFolding.germFarPoint, orient, PiLp.sub_apply, PiLp.zero_apply, sub_zero]
  rfl

/-- Equal projected rays and equal orientation signs identify the actual original germ.
This also handles the negatively oriented terminal bank at a one-sided fan. -/
theorem projected_germ_unique_of_same_orientation (p q : C.LinkGerm Set.univ w)
    (sign : 0 < K.projectedGermOrientation p.val * K.projectedGermOrientation q.val)
    (ray : K.projectedGermRay p = K.projectedGermRay q) : p = q := by
  have product_positive :
      0 < orient 0 (K.projectedGermRay p)
        (K.projectedGermRay (C.linkTurn Set.univ w p)) *
          orient 0 (K.projectedGermRay q)
            (K.projectedGermRay (C.linkTurn Set.univ w q)) := by
    simpa only [K.projectedGermRay_orient] using sign
  have left : orient 0 (K.projectedGermRay p)
      (K.projectedGermRay (C.linkTurn Set.univ w p)) ≠ 0 :=
    left_ne_zero_of_mul product_positive.ne'
  have right : orient 0 (K.projectedGermRay q)
      (K.projectedGermRay (C.linkTurn Set.univ w q)) ≠ 0 :=
    right_ne_zero_of_mul product_positive.ne'
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
    rw [ray, strictRayCone_comm (K.projectedGermRay q)] at separated
    have reversed : orient 0 (K.projectedGermRay (C.linkTurn Set.univ w p))
        (K.projectedGermRay q) =
        -orient 0 (K.projectedGermRay q)
          (K.projectedGermRay (C.linkTurn Set.univ w p)) := by
      simp only [orient, PiLp.zero_apply, sub_zero]
      ring
    rw [ray] at left
    have product := orient_mul_pos_of_disjoint_strictRayCones
      (by rw [reversed]; exact neg_ne_zero.mpr left) right separated
    rw [reversed] at product
    rw [ray] at product_positive
    nlinarith
  have corner : p.val.1 = q.val.1 := congrArg Subtype.val
    (K.cornerAt_face_injective w (a₁ := ⟨p.val.1, p.property⟩)
      (a₂ := ⟨q.val.1, q.property⟩) face)
  apply Subtype.ext
  apply Prod.ext corner
  by_contra sides
  have turned : (C.linkTurn Set.univ w p).val = q.val := by
    change (p.val.1, !p.val.2) = q.val
    refine Prod.ext (by exact corner) ?_
    cases hp : p.val.2 <;> cases hq : q.val.2 <;> simp_all
  have reverse_ray : K.projectedGermRay (C.linkTurn Set.univ w p) = K.projectedGermRay q :=
    congrArg K.projectedGermRay (Subtype.ext turned)
  rw [reverse_ray, ray] at left
  have zero : orient 0 (K.projectedGermRay q) (K.projectedGermRay q) = 0 := by
    simp only [orient, PiLp.zero_apply, sub_zero]
    ring
  exact left zero

/-- In particular, a positive projected outgoing bank determines its raw original germ. -/
theorem projected_positive_germ_unique (p q : C.LinkGerm Set.univ w)
    (positive_p : 0 < K.projectedGermOrientation p.val)
    (positive_q : 0 < K.projectedGermOrientation q.val)
    (ray : K.projectedGermRay p = K.projectedGermRay q) : p = q :=
  K.projected_germ_unique_of_same_orientation p q (mul_pos positive_p positive_q) ray

/-- Physical projected apex and direction data suffice; no choice of original link copy
or face label is supplied. -/
theorem projected_raw_germ_unique (p q : C.Germ)
    (apex : (K.projectedTriangle p.1.1).vertex p.1.2 =
      (K.projectedTriangle q.1.1).vertex q.1.2)
    (sign : 0 < K.projectedGermOrientation p * K.projectedGermOrientation q)
    (direction : Cap.horizontal (K.folding.germDirection p) =
      Cap.horizontal (K.folding.germDirection q)) : p = q := by
  let w := C.vertexOfCorner Set.univ p.1
  let left : C.LinkGerm Set.univ w := ⟨p, rfl⟩
  have at_right : C.vertexOfCorner Set.univ q.1 = w :=
    K.projectedVertex_injective apex.symm
  let right : C.LinkGerm Set.univ w := ⟨q, at_right⟩
  have ray : K.projectedGermRay left = K.projectedGermRay right := by
    rw [← K.horizontal_germDirection left, ← K.horizontal_germDirection right]
    exact direction
  exact congrArg (fun r : C.LinkGerm Set.univ w => r.val)
    (K.projected_germ_unique_of_same_orientation left right sign ray)

end Unfoldings.ConvexCap
