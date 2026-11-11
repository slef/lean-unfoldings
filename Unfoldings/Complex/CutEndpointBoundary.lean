module

public import Unfoldings.Complex.SelectedCuts

/-! Every copy of an original cut endpoint lies on the actual cut bank boundary. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam)

/-- Even copies reached through other retained seams are boundary copies of a cut endpoint. -/
theorem isBoundaryVertex_of_cut_endpoint (w : C.Vertex retain) (s : C.Seam) (cut : s ∉ retain)
    (b : Bool) (endpoint : C.vertexForgetCuts (Set.subset_univ retain) w = C.seamVertex s b) :
    C.IsBoundaryVertex retain w := by
  let inclusion := Set.subset_univ retain
  let y := C.vertexOfCorner retain (C.germOfEndpoint (C.left s) b).1
  have boundary : C.IsBoundaryVertex retain y := by
    cases b
    · exact C.bank_start_isBoundaryVertex retain (C.leftBank retain s cut)
    · exact C.bank_finish_isBoundaryVertex retain (C.leftBank retain s cut)
  have original : C.vertexForgetCuts inclusion y = C.vertexForgetCuts inclusion w := by
    rw [C.vertexForgetCuts_vertexOfCorner]
    exact endpoint.symm
  have equal : C.forgetCuts inclusion (C.vertexPoint retain y) =
      C.forgetCuts inclusion (C.vertexPoint retain w) := by
    rw [← C.vertexPoint_vertexForgetCuts, ← C.vertexPoint_vertexForgetCuts, original]
  have present := (C.vertexPoint_mem_bankBoundary_iff retain y).mpr boundary
  apply (C.vertexPoint_mem_bankBoundary_iff retain w).mp
  rcases C.forgetCuts_fiber_eq_or_boundary inclusion _ _ equal with same | both
  · exact same ▸ present
  · exact both.2

end Unfoldings.TriangleComplex
