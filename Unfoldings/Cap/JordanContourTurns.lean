module

public import Unfoldings.Cap.JordanVertexEnumeration
public import Unfoldings.Cap.JordanAngleBalance

/-!
# Actual ordered boundary turns of intrinsic Jordan fillings

The complete intrinsic contour enumerates the geometric curve's vertices once.
Its real exterior fan turns differ from their projected counterparts by exactly
minus the curvature enclosed by the actual curve. This comparison concerns the
one-sided boundary fans and requires no development of the curved interior.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

open Classical in
/-- The actual intrinsic contour visits each original vertex of the geometric curve once. -/
def jordanContourVertexEquiv :
    Fin ((K.jordanContour jordan contains avoids).length + 1) ≃
      {w : C.Vertex Set.univ // K.projectedVertex w ∈ J} :=
  let Q := K.jordanContour jordan contains avoids
  ((C.restrictFaces (K.jordanFaces J)).boundaryCycleVertexEquiv Set.univ Q.cycle
    Q.closes Q.covers).trans (K.jordanBoundaryVertexEquiv jordan contains avoids)

include jordan contains avoids in
open Classical in
/-- Transfer any original vertex weight to the actual cyclic intrinsic bank order. -/
theorem jordan_contour_sum (weight : C.Vertex Set.univ → ℝ) :
    (∑ i, weight (C.includeRestrictedVertexUniv (K.jordanFaces J)
      ((C.restrictFaces (K.jordanFaces J)).boundaryEndVertex Set.univ
        ((K.jordanContour jordan contains avoids).cycle.point i)))) =
      ∑ w : C.Vertex Set.univ, if K.projectedVertex w ∈ J then weight w else 0 := by
  classical
  change (∑ i, weight ((K.jordanContourVertexEquiv jordan contains avoids) i).val) = _
  rw [(K.jordanContourVertexEquiv jordan contains avoids).sum_comp
    (fun w => weight w.val)]
  rw [← Finset.sum_subtype (p := fun w => K.projectedVertex w ∈ J)
    (Finset.univ.filter (fun w => K.projectedVertex w ∈ J)) (by simp) weight,
    Finset.sum_filter]

include jordan contains avoids in
open Classical in
/-- The difference of the actual two boundary fan angles is the selected original excess. -/
theorem jordan_vertex_angle_excess
    (w : (C.restrictFaces (K.jordanFaces J)).Vertex Set.univ) :
    (C.restrictFaces (K.jordanFaces J)).totalAngle Set.univ w -
      (C.restrictFaces (K.jordanFaces J)).regionalCornerSum Set.univ
        (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w =
      K.regionalAngleExcess (K.jordanFaces J)
        (C.includeRestrictedVertexUniv (K.jordanFaces J) w) := by
  rw [K.jordan_vertex_totalAngle jordan contains avoids,
    K.jordan_vertex_corner_sum jordan contains avoids
      (fun c => (K.projectedTriangle c.1).cornerAngle c.2) w]
  simp only [regionalAngleExcess, TriangleComplex.regionalCornerSum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

include jordan contains avoids in
open Classical in
/-- Exact comparison of actual cyclic exterior fan turns and projected exterior fan turns. -/
theorem jordan_contour_turn_comparison (strictly_inside : J ⊆ interior K.footprint) :
    let R := C.restrictFaces (K.jordanFaces J)
    let Q := K.jordanContour jordan contains avoids
    (∑ i, ((Real.pi - R.totalAngle Set.univ (R.boundaryEndVertex Set.univ (Q.cycle.point i))) -
      (Real.pi - R.regionalCornerSum Set.univ
        (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2)
        (R.boundaryEndVertex Set.univ (Q.cycle.point i))))) =
      -(∑ w : C.Vertex Set.univ,
        if K.projectedVertex w ∈ interior (PlanarTopology.closedJordanDomain J) then
          C.interiorAngularDefect Set.univ w else 0) := by
  classical
  dsimp only
  have local_eq (w : (C.restrictFaces (K.jordanFaces J)).Vertex Set.univ) :
      (Real.pi - (C.restrictFaces (K.jordanFaces J)).totalAngle Set.univ w) -
        (Real.pi - (C.restrictFaces (K.jordanFaces J)).regionalCornerSum Set.univ
          (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w) =
        -K.regionalAngleExcess (K.jordanFaces J)
          (C.includeRestrictedVertexUniv (K.jordanFaces J) w) := by
    have equality := K.jordan_vertex_angle_excess jordan contains avoids w
    linarith
  simp_rw [local_eq]
  rw [Finset.sum_neg_distrib, K.jordan_contour_sum jordan contains avoids,
    K.jordan_boundary_angle_balance jordan strictly_inside avoids]

end Unfoldings.ConvexCap
