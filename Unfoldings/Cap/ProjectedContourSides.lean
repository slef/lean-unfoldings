module

public import Unfoldings.Cap.ProjectionContour

/-!
# The actual projected side of every oriented contour bank

A contour oriented positively in the original projection has its incident
original triangle on the left of every directed outgoing bank. The proof uses
actual face-chart orientation and retained connectivity, so it also applies to
contours whose developed images overlap.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

include D in
/-- Positive original projection orientation propagates around the actual entire bank cycle. -/
theorem projectedGermOrientation_cycle_positive (connected : C.DuallyConnected retain)
    {n : ℕ} (cycle : (C.boundarySystem retain).Chain n)
    (positive : 0 < K.projectedGermOrientation cycle.first.val) (i : Fin (n + 1)) :
    0 < K.projectedGermOrientation (cycle.point i).val := by
  have initial_sign : (0 < D.germOrientation cycle.first.val) ↔
      0 < orientationScale (D.projectedPlacement K cycle.first.val.1.1).toAffineMap := by
    rw [D.germOrientation_eq_projected K]
    exact mul_pos_iff_of_pos_right positive
  have signs : (0 < D.germOrientation (cycle.point i).val) ↔
      0 < orientationScale (D.projectedPlacement K (cycle.point i).val.1.1).toAffineMap :=
    (D.boundaryCycle_orientation cycle i).trans
      (initial_sign.trans (D.projectedPlacement_sign_constant K connected _ _))
  by_cases scale : 0 < orientationScale (D.projectedPlacement K (cycle.point i).val.1.1).toAffineMap
  · have product := signs.mpr scale
    rw [D.germOrientation_eq_projected K] at product
    exact (mul_pos_iff_of_pos_left scale).mp product
  · have scale_negative := lt_of_le_of_ne (le_of_not_gt scale)
      (D.projectedPlacement_scale_ne_zero K (cycle.point i).val.1.1)
    have developed_negative : D.germOrientation (cycle.point i).val < 0 :=
      lt_of_le_of_ne (le_of_not_gt (fun h => scale (signs.mp h)))
        (D.germOrientation_ne_zero (cycle.point i).val)
    rw [D.germOrientation_eq_projected K] at developed_negative
    by_contra nonpositive
    have nonnegative := mul_nonneg_of_nonpos_of_nonpos scale_negative.le
      (le_of_not_gt nonpositive)
    exact not_lt_of_ge nonnegative developed_negative

end Unfoldings.FacewiseDevelopment

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- A positively projected outgoing bank has its entire actual original face on its left. -/
theorem projectedGerm_side_nonneg (p : C.Germ)
    (positive : 0 < K.projectedGermOrientation p) {z : Plane}
    (member : z ∈ (K.projectedTriangle p.1.1).carrier) :
    0 ≤ orient (K.projectFace p.1.1 ((C.triangle p.1.1).vertex p.1.2))
      (K.projectFace p.1.1 ((C.triangle p.1.1).vertex (C.germFarCorner p).2)) z := by
  let height := orientMap
    (K.projectFace p.1.1 ((C.triangle p.1.1).vertex p.1.2))
    (K.projectFace p.1.1 ((C.triangle p.1.1).vertex (C.germFarCorner p).2))
  have convex : Convex ℝ {x | 0 ≤ height x} :=
    (convex_Ici (0 : ℝ)).affine_preimage height
  have contained : (K.projectedTriangle p.1.1).carrier ⊆ {x | 0 ≤ height x} := by
    apply convexHull_min ?_ convex
    rintro x ⟨j, rfl⟩
    obtain ⟨⟨f, i⟩, side⟩ := p
    cases side
    all_goals rcases Triangle.corner_cases i j with rfl | rfl | rfl
    all_goals
      simp only [Set.mem_ofPred_eq, height, orientMap_apply, TriangleComplex.germFarCorner,
        ConvexCap.projectedTriangle, Triangle.affineImage_vertex,
        ConvexCap.projectedGermOrientation,
        TriangleComplex.turnGerm, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ite_true, ite_false, orient_self_left, orient_self_right, le_refl] at positive ⊢
    all_goals exact positive.le
  simpa only [Set.mem_ofPred_eq, height, orientMap_apply] using contained member

end Unfoldings.ConvexCap
