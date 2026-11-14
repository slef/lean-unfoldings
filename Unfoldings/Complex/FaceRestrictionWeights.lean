module

public import Unfoldings.Complex.FaceRestrictionVertices

/-! Exact weighted corner sums over the actual vertex fibers of a whole-face restriction. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

open Classical in
theorem regionalCornerSum_restricted_vertex_fiber (U : Set Face) (weight : C.Corner → ℝ)
    (w : C.Vertex Set.univ) :
    (∑ z : (C.restrictFaces U).Vertex Set.univ,
      if C.includeRestrictedVertexUniv U z = w then
        (C.restrictFaces U).regionalCornerSum Set.univ (fun c => weight (c.1.val, c.2)) z else 0) =
          C.regionalCornerSum U weight w := by
  classical
  let R := C.restrictFaces U
  calc
    _ = ∑ z : R.Vertex Set.univ, ∑ c : R.Corner,
        if R.vertexOfCorner Set.univ c = z ∧ C.includeRestrictedVertexUniv U z = w then
          weight (c.1.val, c.2) else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases same : C.includeRestrictedVertexUniv U z = w
      · simp only [R, same, and_true, ite_true, regionalCornerSum, Set.mem_univ, true_and]
      · simp only [R, same, and_false, ite_false, Finset.sum_const_zero]
    _ = ∑ c : R.Corner, ∑ z : R.Vertex Set.univ,
        if R.vertexOfCorner Set.univ c = z ∧ C.includeRestrictedVertexUniv U z = w then
          weight (c.1.val, c.2) else 0 := Finset.sum_comm
    _ = ∑ c : R.Corner,
        if C.vertexOfCorner Set.univ (c.1.val, c.2) = w then weight (c.1.val, c.2) else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      simp [R, ite_and]
      rfl
    _ = _ := by
      rw [regionalCornerSum, Fintype.sum_prod_type, Fintype.sum_prod_type]
      rw [← Finset.sum_subtype (p := fun f => f ∈ U)
        (Finset.univ.filter (· ∈ U)) (by simp)
        (fun f => ∑ k : Fin 3, if C.vertexOfCorner Set.univ (f, k) = w then weight (f, k) else 0),
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro f _
      by_cases present : f ∈ U <;> simp [present]

end Unfoldings.TriangleComplex
