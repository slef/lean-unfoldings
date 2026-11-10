module

public import Unfoldings.Cap.ProjectedFaces
public import Unfoldings.Complex.Angles

/-!
# Relative angle-defect balance

Original and projected triangles each have angle sum pi. Summing by the same
actual corner classes therefore balances interior defects against boundary
angle excess. The geometric flatness of projected interior links is a separate
hypothesis of the final corollary; no Euler identity is assumed here.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap


universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Projected angles are grouped by the original retained corner classes. -/
def projectedTotalAngle (retain : Set C.Seam) (v : C.Vertex retain) : ℝ := by
  classical
  exact ∑ c : C.Corner,
    if C.vertexOfCorner retain c = v then (K.projectedTriangle c.1).cornerAngle c.2 else 0

theorem sum_projectedTotalAngle (retain : Set C.Seam) :
    ∑ v : C.Vertex retain, K.projectedTotalAngle retain v = Fintype.card Face * Real.pi := by
  classical
  calc
    _ = ∑ c : C.Corner, (K.projectedTriangle c.1).cornerAngle c.2 := by
      simp only [projectedTotalAngle]
      rw [Finset.sum_comm]
      simp
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [Triangle.sum_cornerAngle, nsmul_eq_mul]

open scoped Classical in
/-- Interior angle loss equals boundary angle excess for any specified boundary classes. -/
theorem angleDefect_balance (retain : Set C.Seam) (boundary : Set (C.Vertex retain)) :
    (∑ v : C.Vertex retain, if v ∉ boundary then
      K.projectedTotalAngle retain v - C.totalAngle retain v else 0) =
    ∑ v : C.Vertex retain, if v ∈ boundary then
      C.totalAngle retain v - K.projectedTotalAngle retain v else 0 := by
  classical
  have conservation : (∑ v : C.Vertex retain,
      (K.projectedTotalAngle retain v - C.totalAngle retain v)) = 0 := by
    rw [Finset.sum_sub_distrib, K.sum_projectedTotalAngle, C.sum_totalAngle, sub_self]
  have identity (v : C.Vertex retain) :
      (if v ∉ boundary then K.projectedTotalAngle retain v - C.totalAngle retain v else 0) -
      (if v ∈ boundary then C.totalAngle retain v - K.projectedTotalAngle retain v else 0) =
        K.projectedTotalAngle retain v - C.totalAngle retain v := by
    by_cases present : v ∈ boundary <;> simp [present]
  have equality := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun v _ => identity v)
  rw [Finset.sum_sub_distrib, conservation] at equality
  exact sub_eq_zero.mp equality

open scoped Classical in
/-- Once projected interior links are flat, the same identity is a curvature balance. -/
theorem curvature_eq_boundary_excess (retain : Set C.Seam) (boundary : Set (C.Vertex retain))
    (flat : ∀ v ∉ boundary, K.projectedTotalAngle retain v = 2 * Real.pi) :
    (∑ v : C.Vertex retain, if v ∉ boundary then
      2 * Real.pi - C.totalAngle retain v else 0) =
    ∑ v : C.Vertex retain, if v ∈ boundary then
      C.totalAngle retain v - K.projectedTotalAngle retain v else 0 := by
  classical
  rw [← K.angleDefect_balance retain boundary]
  apply Finset.sum_congr rfl
  intro v _
  by_cases present : v ∈ boundary
  · simp [present]
  · simp [present, flat v present]

end Unfoldings.ConvexCap
