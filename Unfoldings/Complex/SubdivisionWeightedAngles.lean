module

public import Unfoldings.Complex.SubdivisionCornerAngles
public import Unfoldings.Complex.RegionalCorners

/-! Exact refinement angle sums preserve arbitrary original face weights and regional fans. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex.Subdivision

universe u v w z

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child} (S : C.Subdivision D)

open Classical in
/-- Any weight attached to original faces is conserved at each individual old corner. -/
theorem sum_weighted_refined_corner_angles (preserving : S.CornerAnglePreserving)
    (weight : Face → ℝ) (c : C.Corner) :
    (∑ d : D.Corner, if S.RefinesCorner d c then
      weight (S.parent d.1) * (D.triangle d.1).cornerAngle d.2 else 0) =
        weight c.1 * (C.triangle c.1).cornerAngle c.2 := by
  classical
  rw [← preserving c, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  by_cases matched : S.RefinesCorner d c
  · simp only [matched, ite_true, matched.1]
  · simp only [matched, ite_false, mul_zero]

open Classical in
/-- Arbitrary original face weights pass through the actual metric image of each cut vertex. -/
theorem sum_weighted_angles_over_parent_vertex (preserving : S.CornerAnglePreserving)
    (weight : Face → ℝ) (retain : Set C.Seam) (vertex : C.Vertex retain) :
    (∑ d : D.Corner,
      if MetricGluing.point C.Cell (C.glue retain) (S.parentPoint (D.cornerPoint d)) =
        C.vertexPoint retain vertex then
          weight (S.parent d.1) * (D.triangle d.1).cornerAngle d.2 else 0) =
      ∑ c : C.Corner, if C.vertexOfCorner retain c = vertex then
        weight c.1 * (C.triangle c.1).cornerAngle c.2 else 0 := by
  classical
  simp_rw [S.parent_vertex_weight_eq_corner_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  by_cases same : C.vertexOfCorner retain c = vertex
  · simp only [same, ite_true]
    exact S.sum_weighted_refined_corner_angles preserving weight c
  · simp only [same, ite_false, Finset.sum_const_zero]

open Classical in
/-- A union of whole original faces carries precisely its original regional fan angle. -/
theorem sum_angles_over_parent_vertex_in_faces (preserving : S.CornerAnglePreserving)
    (faces : Set Face) (vertex : C.Vertex Set.univ) :
    (∑ d : D.Corner,
      if S.parent d.1 ∈ faces ∧
        MetricGluing.point C.Cell (C.glue Set.univ) (S.parentPoint (D.cornerPoint d)) =
          C.vertexPoint Set.univ vertex then (D.triangle d.1).cornerAngle d.2 else 0) =
      C.regionalCornerSum faces (fun c => (C.triangle c.1).cornerAngle c.2) vertex := by
  classical
  have weighted := S.sum_weighted_angles_over_parent_vertex preserving
    (fun f => if f ∈ faces then 1 else 0) Set.univ vertex
  convert weighted using 1
  · apply Finset.sum_congr rfl
    intro d _
    by_cases present : S.parent d.1 ∈ faces <;>
      by_cases same : MetricGluing.point C.Cell (C.glue Set.univ)
        (S.parentPoint (D.cornerPoint d)) = C.vertexPoint Set.univ vertex <;>
      simp only [present, same, and_self, and_true, and_false, ite_true, ite_false,
        one_mul, zero_mul]
  · unfold TriangleComplex.regionalCornerSum
    apply Finset.sum_congr rfl
    intro c _
    by_cases present : c.1 ∈ faces <;>
      by_cases same : C.vertexOfCorner Set.univ c = vertex <;>
      simp only [present, same, and_self, and_true, and_false, ite_true, ite_false,
        one_mul, zero_mul]

end Unfoldings.TriangleComplex.Subdivision
