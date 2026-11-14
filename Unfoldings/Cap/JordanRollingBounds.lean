module

public import Unfoldings.Cap.JordanRolling
public import Mathlib.Algebra.BigOperators.Intervals

/-! Actual real bank-heading discrepancies inherit the geometric Jordan curvature bound. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
theorem jordanRollHeadingError_step
    (i : Fin (K.jordanContour jordan contains avoids).length) :
    K.jordanRollHeadingError jordan contains avoids i.succ -
      K.jordanRollHeadingError jordan contains avoids i.castSucc =
        K.jordanContourTurnError jordan contains avoids i.succ := by
  rw [K.jordanRollHeadingError_eq_partialSum, K.jordanRollHeadingError_eq_partialSum,
    Fin.partialSum_succ]
  ring

include jordan contains avoids in
open Classical in
/-- A contiguous bank's real heading change records every intermediate actual corner once. -/
theorem jordanRollHeadingError_sub_eq_sum
    {a b : Fin (K.jordanContour jordan contains avoids).length} (ordered : a ≤ b) :
    K.jordanRollHeadingError jordan contains avoids b.succ -
      K.jordanRollHeadingError jordan contains avoids a.castSucc =
        ∑ i ∈ Finset.Icc a.succ b.succ, K.jordanContourTurnError jordan contains avoids i := by
  rw [Fin.sum_Icc_succ]
  simp_rw [← K.jordanRollHeadingError_step jordan contains avoids]
  exact (Fin.sum_Icc_sub ordered (K.jordanRollHeadingError jordan contains avoids)).symm

include jordan contains avoids in
open Classical in
/-- Enclosed curvature and closing-link error bound actual unreduced bank-heading change. -/
theorem abs_jordanRollHeadingError_sub_le (strictly_inside : J ⊆ interior K.footprint)
    {a b : Fin (K.jordanContour jordan contains avoids).length} (ordered : a ≤ b) {B : ℝ}
    (closing : |∑ i ∈ (Finset.Icc a.succ b.succ)ᶜ,
      K.jordanContourTurnError jordan contains avoids i| ≤ B) :
    |K.jordanRollHeadingError jordan contains avoids b.succ -
      K.jordanRollHeadingError jordan contains avoids a.castSucc| ≤
        C.totalInteriorAngularDefect Set.univ + B := by
  rw [K.jordanRollHeadingError_sub_eq_sum jordan contains avoids ordered]
  exact K.abs_jordan_bank_turn_error_le jordan contains avoids strictly_inside _ closing

end Unfoldings.ConvexCap
