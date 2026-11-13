module

public import Unfoldings.Roof.ProjectedLink
public import Unfoldings.Geometry.ComplexArea

/-!
# Projected interior links are flat

The actual cyclic projected edge rays have disjoint genuine cones. Their
angles make precisely one full turn, so the projected total angle at every
interior vertex is 2 pi. The relative angle balance therefore gives the actual
cap curvature/boundary-excess identity without an assumed flatness certificate.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem projectedGermRay_orient_ne_zero {v : C.Vertex Set.univ} (p : C.LinkGerm Set.univ v) :
    orient 0 (K.projectedGermRay p)
      (K.projectedGermRay (C.linkTurn Set.univ v p)) ≠ 0 := by
  have apex := K.projectedGerm_apex p
  obtain ⟨⟨⟨f, i⟩, side⟩, hp⟩ := p
  cases side
  · change orient 0
      ((K.projectedTriangle f).vertex (Triangle.next i) - K.projectedVertex v)
      ((K.projectedTriangle f).vertex (Triangle.next (Triangle.next i)) - K.projectedVertex v) ≠ 0
    rw [← apex]
    have identity (a b c : Plane) : orient 0 (b - a) (c - a) = orient a b c := by
      simp only [orient, PiLp.sub_apply, PiLp.zero_apply, sub_zero]
    rw [identity]
    exact (K.projectedTriangle f).orient_edge_ne_zero i
  · change orient 0
      ((K.projectedTriangle f).vertex (Triangle.next (Triangle.next i)) - K.projectedVertex v)
      ((K.projectedTriangle f).vertex (Triangle.next i) - K.projectedVertex v) ≠ 0
    rw [← apex]
    have identity (a b c : Plane) : orient 0 (c - a) (b - a) = -orient a b c := by
      simp only [orient, PiLp.sub_apply, PiLp.zero_apply, sub_zero]
      ring
    rw [identity]
    exact neg_ne_zero.mpr ((K.projectedTriangle f).orient_edge_ne_zero i)

variable {v : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)

/-- The actual projected cyclic fan makes exactly one full turn, in either orientation. -/
theorem projectedLinkFan_full_turn
    (closes : C.linkMate Set.univ v (C.linkTurn Set.univ v c.last) = c.first)
    (covers : ∀ p, c.Visited p) : (K.projectedLinkFan c).totalAngle = 2 * Real.pi := by
  let L : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let ray (i : Fin (n + 1)) : ℂ := L (K.projectedGermRay (c.point i))
  have angles (i : Fin (n + 1)) :
      InnerProductGeometry.angle (ray i) (ray (finRotate (n + 1) i)) =
        (K.projectedLinkFan c).angle i :=
    (L.toLinearIsometry.angle_map _ _).trans (K.projectedLinkFan_ray_angle c closes i)
  have genuine (i : Fin (n + 1)) :
      (starRingEnd ℂ (ray i) * ray (finRotate (n + 1) i)).im ≠ 0 := by
    have nonzero := K.projectedGermRay_orient_ne_zero (c.point i)
    rw [K.projectedGermRay_chain_rotates c closes i] at nonzero
    have identity := orient_complex_repr_zero (ray i) (ray (finRotate (n + 1) i))
    change orient 0 (L.symm (L (K.projectedGermRay (c.point i))))
      (L.symm (L (K.projectedGermRay (c.point (finRotate (n + 1) i))))) = _ at identity
    rw [L.symm_apply_apply, L.symm_apply_apply] at identity
    rwa [identity] at nonzero
  apply (K.projectedLinkFan c).totalAngle_eq_two_pi_of_disjoint_cyclic_rays ray angles genuine
  intro i j different
  change Disjoint
    (strictRayCone (L.toLinearMap (K.projectedGermRay (c.point i)))
      (L.toLinearMap (K.projectedGermRay (c.point (finRotate (n + 1) i)))))
    (strictRayCone (L.toLinearMap (K.projectedGermRay (c.point j)))
      (L.toLinearMap (K.projectedGermRay (c.point (finRotate (n + 1) j)))))
  rw [← L.toLinearMap.image_strictRayCone, ← L.toLinearMap.image_strictRayCone]
  exact (Set.disjoint_image_iff L.injective).mpr
    (K.projectedLinkFan_cones_disjoint c closes covers different)

/-- Flatness of the projected link follows from the actual cap geometry. -/
theorem projectedTotalAngle_eq_two_pi (v : C.Vertex Set.univ)
    (internal : ¬ C.IsBoundaryVertex Set.univ v) :
    K.projectedTotalAngle Set.univ v = 2 * Real.pi := by
  obtain ⟨n, c, closes, covers⟩ := C.exists_cyclic_link Set.univ v internal
  rw [← K.projectedLinkFan_totalAngle c covers]
  exact K.projectedLinkFan_full_turn c closes covers

open scoped Classical in
/-- Total interior intrinsic angle defect equals the actual boundary angle excess. -/
theorem curvature_eq_actual_boundary_excess :
    (∑ v : C.Vertex Set.univ, if ¬ C.IsBoundaryVertex Set.univ v then
      2 * Real.pi - C.totalAngle Set.univ v else 0) =
    ∑ v : C.Vertex Set.univ, if C.IsBoundaryVertex Set.univ v then
      C.totalAngle Set.univ v - K.projectedTotalAngle Set.univ v else 0 :=
  K.curvature_eq_boundary_excess Set.univ {v | C.IsBoundaryVertex Set.univ v}
    (fun v internal => K.projectedTotalAngle_eq_two_pi v internal)

end Unfoldings.ConvexRoof
