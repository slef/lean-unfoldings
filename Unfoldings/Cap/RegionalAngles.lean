module

public import Unfoldings.Complex.RegionalCorners
public import Unfoldings.Cap.RimAngles

/-!
# Relative angle balance for every actual union of original faces

The total excess on the partial corner stars is bounded by the complete cap
curvature. No assumed disk region, boundary order, or Euler count is input.
Relating these stars to a chosen cut path is a separate geometric step.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Intrinsic minus projected angles contributed by the selected original face corners. -/
def regionalAngleExcess (faces : Set Face) (v : C.Vertex Set.univ) : ℝ :=
  C.regionalCornerSum faces
    (fun c => (C.triangle c.1).cornerAngle c.2 - (K.projectedTriangle c.1).cornerAngle c.2) v

theorem sum_regionalAngleExcess (faces : Set Face) :
    (∑ v : C.Vertex Set.univ, K.regionalAngleExcess faces v) = 0 := by
  classical
  simp only [regionalAngleExcess]
  rw [C.sum_regionalCornerSum, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro f _
  by_cases present : f ∈ faces
  · simp only [present, ite_eq_left, Finset.sum_sub_distrib,
      Triangle.sum_cornerAngle, sub_self]
  · simp [present]

theorem regionalAngleExcess_of_fullStar (faces : Set Face) (v : C.Vertex Set.univ)
    (full : C.FullStarIn faces v) : K.regionalAngleExcess faces v =
      C.totalAngle Set.univ v - K.projectedTotalAngle Set.univ v := by
  classical
  rw [regionalAngleExcess, C.regionalCornerSum_of_fullStar faces _ v full]
  simp only [TriangleComplex.totalAngle, projectedTotalAngle, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases same : C.vertexOfCorner Set.univ c = v <;> simp [same]

open scoped Classical in
/-- Partial stars carry exactly the remaining difference between interior and rim contributions. -/
theorem regional_partialStar_balance (faces : Set Face) :
    (∑ v : C.Vertex Set.univ, if ¬ C.FullStarIn faces v then K.regionalAngleExcess faces v else 0) =
      (∑ v : C.Vertex Set.univ,
        if C.FullStarIn faces v then C.interiorAngularDefect Set.univ v else 0) -
        ∑ v : C.Vertex Set.univ, if C.FullStarIn faces v then K.boundaryAngleExcess v else 0 := by
  classical
  have identity (v : C.Vertex Set.univ) : K.regionalAngleExcess faces v =
      (if ¬ C.FullStarIn faces v then K.regionalAngleExcess faces v else 0) +
      (if C.FullStarIn faces v then K.boundaryAngleExcess v else 0) -
      (if C.FullStarIn faces v then C.interiorAngularDefect Set.univ v else 0) := by
    by_cases full : C.FullStarIn faces v
    · rw [K.regionalAngleExcess_of_fullStar faces v full]
      by_cases boundary : C.IsBoundaryVertex Set.univ v
      · simp [full, boundary, boundaryAngleExcess, TriangleComplex.interiorAngularDefect]
      · simp [full, boundary, boundaryAngleExcess, TriangleComplex.interiorAngularDefect,
          K.projectedTotalAngle_eq_two_pi v boundary]
    · simp only [full, not_false_eq_true, ite_eq_left, ite_eq_right, add_zero, sub_zero]
  have total := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun v _ => identity v)
  rw [K.sum_regionalAngleExcess faces, Finset.sum_sub_distrib, Finset.sum_add_distrib] at total
  linarith

open scoped Classical in
/-- Uniform absolute control of the aggregate partial-star angle distortion for every face union. -/
theorem abs_regional_partialStar_excess_le (faces : Set Face) :
    |∑ v : C.Vertex Set.univ,
      if ¬ C.FullStarIn faces v then K.regionalAngleExcess faces v else 0| ≤
        C.totalInteriorAngularDefect Set.univ := by
  classical
  have interior_nonnegative : 0 ≤ ∑ v : C.Vertex Set.univ,
      if C.FullStarIn faces v then C.interiorAngularDefect Set.univ v else 0 :=
    Finset.sum_nonneg (fun v _ => by
      split_ifs <;> simp only [K.interiorCurvature_nonneg, le_refl])
  have rim_nonnegative : 0 ≤ ∑ v : C.Vertex Set.univ,
      if C.FullStarIn faces v then K.boundaryAngleExcess v else 0 :=
    Finset.sum_nonneg (fun v _ => by
      split_ifs <;> simp only [K.boundaryAngleExcess_nonneg, le_refl])
  have interior_bound : (∑ v : C.Vertex Set.univ,
      if C.FullStarIn faces v then C.interiorAngularDefect Set.univ v else 0) ≤
        C.totalInteriorAngularDefect Set.univ := by
    unfold TriangleComplex.totalInteriorAngularDefect
    apply Finset.sum_le_sum
    intro v _
    split_ifs <;> simp only [le_refl, K.interiorCurvature_nonneg]
  have rim_bound : (∑ v : C.Vertex Set.univ,
      if C.FullStarIn faces v then K.boundaryAngleExcess v else 0) ≤
        C.totalInteriorAngularDefect Set.univ := by
    rw [← K.sum_boundaryAngleExcess]
    apply Finset.sum_le_sum
    intro v _
    split_ifs <;> simp only [le_refl, K.boundaryAngleExcess_nonneg]
  rw [K.regional_partialStar_balance, abs_le]
  constructor <;> linarith

end Unfoldings.ConvexCap
