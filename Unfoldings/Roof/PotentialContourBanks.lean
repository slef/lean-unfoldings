module

public import Unfoldings.Roof.PotentialContourHistory
public import Unfoldings.Roof.BoundaryFaceValues
public import Unfoldings.Polyhedron.ProjectedBoundaryChain
public import Unfoldings.Polyhedron.BoundaryDirections
public import Unfoldings.Complex.FreshSourceContourBanks
public import Unfoldings.Complex.ContourGapBankIndex

/-! The actual saved-frontier banks of a potential cut forest follow its exact parent history. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.PotentialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {f : Plane → ℝ} {cuts : Set Plane} (R : K.PotentialCutForest f cuts)
  (Q : C.BoundaryContour (C.selectedRetain R.selection))
  (starts : C.contourOriginalVertex R.selection Q 0 ∈ R.parents.roots)
  (event : C.PositiveContourSource R.selection Q)

local notation "Source" => C.positiveContourVertex R.selection Q event
local notation "Length" => C.positiveContourBankLength R.selection Q event
local notation "Retain" =>
  C.processedParentRetain R.selection (C.contourFrontier R.selection Q event.val.succ)

include starts in
theorem exists_contourSourceBankChain :
    ∃ bank : (C.boundarySystem Retain).Chain Length,
      (∀ i, C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex _ (bank.point i)) = R.parents.parent^[i.val] Source) ∧
      C.vertexForgetCuts (Set.subset_univ _)
        (C.boundaryEndVertex _ (C.boundaryTurn _ bank.last)) = R.parents.root Source ∧
      ∀ i, ∃ j : Fin (Q.length + 1), event.val.val ≤ j.val ∧
        (bank.point i).val = (Q.cycle.point j).val :=
  K.folding.exists_contourSourceBankChain R.selection R.boundary_roots Q starts
    event.val event.property.1 Length (C.positiveContourBank_span R.selection Q event)

/-- The source-inclusive bank at the actual saved stage of this contour. -/
def contourSourceBankChain : (C.boundarySystem Retain).Chain Length :=
  (exists_contourSourceBankChain R Q starts event).choose

local notation "Bank" => R.contourSourceBankChain Q starts event

theorem contourSourceBankChain_original (i : Fin (Length + 1)) :
    C.vertexForgetCuts (Set.subset_univ _)
      (C.boundaryEndVertex _ ((Bank).point i)) = R.parents.parent^[i.val] Source :=
  (exists_contourSourceBankChain R Q starts event).choose_spec.1 i

theorem contourSourceBankChain_contour (i : Fin (Length + 1)) :
    ∃ j : Fin (Q.length + 1), event.val.val ≤ j.val ∧ ((Bank).point i).val = (Q.cycle.point j).val :=
  (exists_contourSourceBankChain R Q starts event).choose_spec.2.2 i

private theorem projected_bank_position {retain : Set C.Seam} (p : C.BoundaryEnd retain) :
    Cap.horizontal (K.folding.boundaryPosition p) =
      K.projectedVertex (C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex retain p)) := by
  rw [K.folding.boundaryPosition_raw]
  simp only [TriangleComplex.boundaryEndVertex, C.vertexForgetCuts_vertexOfCorner,
    K.projectedVertex_ofCorner, K.projectedTriangle_vertex]

/-- The physical bank visits the exact iterates of the fine parent map, including the rim end. -/
theorem contourSourceBankChain_projected_vertex (i : Fin (Length + 2)) :
    (K.folding.projectedBoundaryChain Bank).vertex i =
      K.projectedVertex (R.parents.parent^[i.val] Source) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have terminal :
        C.vertexForgetCuts (Set.subset_univ _)
          (C.boundaryEndVertex _ (C.boundaryTurn _ (Bank).last)) = R.parents.root Source :=
      (exists_contourSourceBankChain R Q starts event).choose_spec.2.1
    rw [K.folding.projectedBoundaryChain_vertex_last, projected_bank_position, terminal,
      Fin.val_last, ← C.positiveContourBank_span R.selection Q event,
      R.parents.iterate_distanceToRoot_eq_root]
  · rw [K.folding.projectedBoundaryChain_vertex_castSucc, projected_bank_position,
      R.contourSourceBankChain_original Q starts event, Fin.val_castSucc]

/-- Every bank starts at a genuine cut. The endpoint of its final such cut may be on the rim. -/
theorem contourSourceBankChain_cut (i : Fin (Length + 1)) :
    ¬ C.IsBoundaryEdge Set.univ (C.germEdge ((Bank).point i).val) := by
  intro boundary
  have original := C.isBoundaryVertex_of_boundary_germ Set.univ ((Bank).point i).val boundary
  have root : C.vertexForgetCuts (Set.subset_univ _) (C.boundaryEndVertex _ ((Bank).point i)) ∈
      R.parents.roots := R.boundary_roots (by
    simpa only [TriangleComplex.boundaryEndVertex, TriangleComplex.vertexForgetCuts_vertexOfCorner,
      TriangleComplex.relativeCutRoots, Set.mem_ofPred_eq] using original)
  rw [R.contourSourceBankChain_original Q starts event] at root
  exact R.parents.iterate_lt_distanceToRoot_not_mem Source
    (by rw [C.positiveContourBank_span R.selection Q event]; exact i.isLt) root

end Unfoldings.ConvexRoof.PotentialCutForest
