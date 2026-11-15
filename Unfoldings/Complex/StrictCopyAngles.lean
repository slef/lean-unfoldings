module

public import Unfoldings.Complex.AngleCutSums
public import Unfoldings.Complex.InteriorCopyAngles

/-! A genuinely split cut vertex has a boundary fan strictly smaller than its original full star. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large)

/-- A distinct sibling cut copy has positive angle, making this copy strictly smaller. -/
theorem totalAngle_lt_forgetCuts_of_other_copy (w z : C.Vertex small) (distinct : w ≠ z)
    (same : C.vertexForgetCuts inclusion z = C.vertexForgetCuts inclusion w) :
    C.totalAngle small w < C.totalAngle large (C.vertexForgetCuts inclusion w) := by
  classical
  let f (x : C.Vertex small) := if C.vertexForgetCuts inclusion x =
    C.vertexForgetCuts inclusion w then C.totalAngle small x else 0
  have nonnegative (x : C.Vertex small) : 0 ≤ f x := by
    dsimp [f]
    split_ifs
    · exact (C.totalAngle_pos small x).le
    · exact le_rfl
  have bound : f w + f z ≤ ∑ x, f x := by
    calc
      _ = ∑ x ∈ ({w, z} : Finset (C.Vertex small)), f x := by simp [distinct]
      _ ≤ ∑ x, f x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _hx _none => nonnegative x)
  have total := C.sum_totalAngle_vertexForgetCuts inclusion (C.vertexForgetCuts inclusion w)
  change (∑ x, f x) = _ at total
  have first : f w = C.totalAngle small w := by simp [f]
  have last : f z = C.totalAngle small z := by simp [f, same]
  rw [total, first, last] at bound
  linarith [C.totalAngle_pos small z]

/-- Splitting into more than one actual copy forces each such copy onto the cut boundary. -/
theorem isBoundaryVertex_of_other_cut_copy (w z : C.Vertex small) (distinct : w ≠ z)
    (same : C.vertexForgetCuts inclusion z = C.vertexForgetCuts inclusion w) :
    C.IsBoundaryVertex small w := by
  by_contra internal
  exact distinct (C.vertexForgetCuts_fiber_eq_of_internal inclusion w internal same).symm

end Unfoldings.TriangleComplex
