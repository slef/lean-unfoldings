module

public import Unfoldings.Cap.JordanContourTurns

/-!
# One-sided bank turn error from the actual Jordan closure

The complete contour's error lies between minus total curvature and zero.
Consequently a bank subchain's aggregate error is bounded by total curvature
plus the aggregate error on its complementary closing links. The estimate
counts no mesh vertices or triangles.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

open Classical in
/-- Actual intrinsic exterior fan turn minus projected exterior fan turn, in cyclic order. -/
def jordanContourTurnError (i : Fin ((K.jordanContour jordan contains avoids).length + 1)) : ℝ :=
  let R := C.restrictFaces (K.jordanFaces J)
  let w := R.boundaryEndVertex Set.univ ((K.jordanContour jordan contains avoids).cycle.point i)
  (Real.pi - R.totalAngle Set.univ w) -
    (Real.pi - R.regionalCornerSum Set.univ
      (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w)

include jordan contains avoids in
open Classical in
/-- The actual full contour error has a sign as well as a mesh-independent curvature bound. -/
theorem jordan_contour_turn_error_bounds (strictly_inside : J ⊆ interior K.footprint) :
    -C.totalInteriorAngularDefect Set.univ ≤
      ∑ i, K.jordanContourTurnError jordan contains avoids i ∧
    (∑ i, K.jordanContourTurnError jordan contains avoids i) ≤ 0 := by
  classical
  have equality := K.jordan_contour_turn_comparison jordan contains avoids strictly_inside
  change (∑ i, K.jordanContourTurnError jordan contains avoids i) = _ at equality
  have nonnegative : 0 ≤ ∑ w : C.Vertex Set.univ,
      if K.projectedVertex w ∈ interior (PlanarTopology.closedJordanDomain J) then
        C.interiorAngularDefect Set.univ w else 0 := by
    apply Finset.sum_nonneg
    intro w _
    split_ifs <;> simp only [K.interiorCurvature_nonneg, le_refl]
  have bound : (∑ w : C.Vertex Set.univ,
      if K.projectedVertex w ∈ interior (PlanarTopology.closedJordanDomain J) then
        C.interiorAngularDefect Set.univ w else 0) ≤ C.totalInteriorAngularDefect Set.univ := by
    unfold TriangleComplex.totalInteriorAngularDefect
    apply Finset.sum_le_sum
    intro w _
    split_ifs <;> simp only [le_refl, K.interiorCurvature_nonneg]
  rw [equality]
  constructor <;> linarith

include jordan contains avoids in
open Classical in
/-- Closing-link error controls any bank portion of the actual ordered intrinsic boundary. -/
theorem jordan_bank_turn_error_bounds (strictly_inside : J ⊆ interior K.footprint)
    (bank : Finset (Fin ((K.jordanContour jordan contains avoids).length + 1))) {B : ℝ}
    (closing : |∑ i ∈ bankᶜ, K.jordanContourTurnError jordan contains avoids i| ≤ B) :
    -C.totalInteriorAngularDefect Set.univ - B ≤
      ∑ i ∈ bank, K.jordanContourTurnError jordan contains avoids i ∧
    (∑ i ∈ bank, K.jordanContourTurnError jordan contains avoids i) ≤ B := by
  classical
  have total := K.jordan_contour_turn_error_bounds jordan contains avoids strictly_inside
  have partition := Finset.sum_add_sum_compl bank
    (fun i => K.jordanContourTurnError jordan contains avoids i)
  obtain ⟨lower, upper⟩ := abs_le.mp closing
  constructor <;> linarith [total.1, total.2]

include jordan contains avoids in
open Classical in
/-- The absolute one-sided bank error is at most curvature plus the closing-link error. -/
theorem abs_jordan_bank_turn_error_le (strictly_inside : J ⊆ interior K.footprint)
    (bank : Finset (Fin ((K.jordanContour jordan contains avoids).length + 1))) {B : ℝ}
    (closing : |∑ i ∈ bankᶜ, K.jordanContourTurnError jordan contains avoids i| ≤ B) :
    |∑ i ∈ bank, K.jordanContourTurnError jordan contains avoids i| ≤
      C.totalInteriorAngularDefect Set.univ + B := by
  have bounds := K.jordan_bank_turn_error_bounds jordan contains avoids strictly_inside bank closing
  have nonnegative : 0 ≤ C.totalInteriorAngularDefect Set.univ :=
    Finset.sum_nonneg (fun w _ => K.interiorCurvature_nonneg w)
  rw [abs_le]
  constructor <;> linarith

end Unfoldings.ConvexCap
