module

public import Unfoldings.Complex.Angles

/-!
# Summing actual corner angles after cuts

Restoring seams groups the actual cut-copy angles without changing their sum.
Weighted and regional versions keep this accounting independent of the number
of cuts and of any development.
-/

@[expose] public section

noncomputable section


namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large)

/-- Cutting only removes corner contributions from a given vertex copy. -/
theorem totalAngle_le_forgetCuts (w : C.Vertex small) :
    C.totalAngle small w ≤ C.totalAngle large (C.vertexForgetCuts inclusion w) := by
  classical
  rw [← C.sum_totalAngle_vertexForgetCuts inclusion]
  have bound := Finset.single_le_sum
    (f := fun x : C.Vertex small => if C.vertexForgetCuts inclusion x =
      C.vertexForgetCuts inclusion w then C.totalAngle small x else 0)
    (fun x _ => by split_ifs <;> first | exact (C.totalAngle_pos small x).le | rfl)
    (Finset.mem_univ w)
  simpa only [ite_true] using bound

/-- Any weight on original vertex classes can be summed over their actual cut copies. -/
theorem sum_weighted_totalAngle_forgetCuts (weight : C.Vertex large → ℝ) :
    (∑ w : C.Vertex small, weight (C.vertexForgetCuts inclusion w) * C.totalAngle small w) =
      ∑ v : C.Vertex large, weight v * C.totalAngle large v := by
  classical
  simp only [totalAngle, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  simp [C.vertexForgetCuts_vertexOfCorner]

open scoped Classical in
/-- All the cut copies of any chosen original vertex set carry its full original angle. -/
theorem sum_totalAngle_over_copies (vertices : Finset (C.Vertex large)) :
    (∑ w : C.Vertex small,
      if C.vertexForgetCuts inclusion w ∈ vertices then C.totalAngle small w else 0) =
        ∑ v ∈ vertices, C.totalAngle large v := by
  classical
  have weighted := C.sum_weighted_totalAngle_forgetCuts inclusion
    (fun v => if v ∈ vertices then 1 else 0)
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter] using weighted

end Unfoldings.TriangleComplex
