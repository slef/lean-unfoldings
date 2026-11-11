module

public import Unfoldings.Complex.Angles
public import Unfoldings.Complex.BoundaryQuotient
public import Unfoldings.Complex.RelativeSeamGeometry

/-! A vertex copy still in the cut interior retains the entire original corner angle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {small large : Set C.Seam} (inclusion : small ⊆ large)

/-- Cutting can split a vertex only into boundary copies. -/
theorem vertexForgetCuts_fiber_eq_of_internal (w : C.Vertex small)
    (internal : ¬ C.IsBoundaryVertex small w) {x : C.Vertex small}
    (same : C.vertexForgetCuts inclusion x = C.vertexForgetCuts inclusion w) : x = w := by
  have equal : C.forgetCuts inclusion (C.vertexPoint small x) =
      C.forgetCuts inclusion (C.vertexPoint small w) := by
    rw [← C.vertexPoint_vertexForgetCuts, ← C.vertexPoint_vertexForgetCuts, same]
  rcases C.forgetCuts_fiber_eq_or_boundary inclusion _ _ equal with same_point | boundary
  · exact C.vertexPoint_injective small same_point
  · exact (internal ((C.vertexPoint_mem_bankBoundary_iff small w).mp boundary.2)).elim

/-- Every corner above an internal copy remains in that copy. -/
theorem totalAngle_eq_of_internal_copy (w : C.Vertex small)
    (internal : ¬ C.IsBoundaryVertex small w) :
    C.totalAngle small w = C.totalAngle large (C.vertexForgetCuts inclusion w) := by
  classical
  have fiber (x : C.Vertex small) :
      C.vertexForgetCuts inclusion x = C.vertexForgetCuts inclusion w ↔ x = w :=
    ⟨C.vertexForgetCuts_fiber_eq_of_internal inclusion w internal,
      fun same => congrArg (C.vertexForgetCuts inclusion) same⟩
  rw [← C.sum_totalAngle_vertexForgetCuts inclusion]
  simp only [fiber, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Unfoldings.TriangleComplex
