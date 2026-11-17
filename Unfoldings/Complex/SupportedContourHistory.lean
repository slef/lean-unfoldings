module

public import Unfoldings.Complex.SelectedContourHistory
public import Unfoldings.Complex.ParentBankEndpoints

/-! Complete original contour histories allow unused isolated vertices to be marked as roots. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)

/-- Every actual copy of a nonroot is on the original cut boundary. Unused isolated roots
need not lie on the rim or be visited by the boundary contour. -/
theorem selectedCut_nonroot_copy_boundary (w : C.Vertex (C.selectedRetain S))
    (nonroot : C.vertexForgetCuts (Set.subset_univ _) w ∉ P.roots) :
    C.IsBoundaryVertex (C.selectedRetain S) w := by
  let inclusion := Set.subset_univ (C.selectedRetain S)
  let v := C.vertexForgetCuts inclusion w
  apply (C.vertexPoint_mem_bankBoundary_iff (C.selectedRetain S) w).mp
  let a : {v : C.Vertex Set.univ // v ∉ P.roots} := ⟨v, nonroot⟩
  let s := S.edge a
  have cut : s ∉ C.selectedRetain S := fun outside => outside ⟨a, rfl⟩
  have endpoint_boundary (b : Bool) (endpoint : v = C.seamVertex s b) :
      C.vertexPoint (C.selectedRetain S) w ∈ C.bankBoundary (C.selectedRetain S) := by
    let y := C.vertexOfCorner (C.selectedRetain S) (C.germOfEndpoint (C.left s) b).1
    have boundary : C.IsBoundaryVertex (C.selectedRetain S) y := by
      cases b
      · exact C.bank_start_isBoundaryVertex _ (C.leftBank _ s cut)
      · exact C.bank_finish_isBoundaryVertex _ (C.leftBank _ s cut)
    have original : C.vertexForgetCuts inclusion y = v := by
      change C.vertexForgetCuts inclusion
        (C.vertexOfCorner (C.selectedRetain S) (C.germOfEndpoint (C.left s) b).1) = v
      rw [C.vertexForgetCuts_vertexOfCorner]
      exact endpoint.symm
    have equal : C.forgetCuts inclusion (C.vertexPoint (C.selectedRetain S) y) =
        C.forgetCuts inclusion (C.vertexPoint (C.selectedRetain S) w) := by
      rw [← C.vertexPoint_vertexForgetCuts, ← C.vertexPoint_vertexForgetCuts, original]
    have present := (C.vertexPoint_mem_bankBoundary_iff (C.selectedRetain S) y).mpr boundary
    rcases C.forgetCuts_fiber_eq_or_boundary inclusion _ _ equal with same | both
    · exact same ▸ present
    · exact both.2
  have link := S.link a
  rcases link with first | last
  · exact endpoint_boundary false first.1
  · exact endpoint_boundary true last.1

variable (Q : C.BoundaryContour (C.selectedRetain S))

/-- The actual contour visits every nonroot, even when some isolated roots are unused. -/
theorem mem_selectedContourSeeds_of_nonroot (v : C.Vertex Set.univ) (nonroot : v ∉ P.roots) :
    v ∈ C.selectedContourSeeds S Q := by
  obtain ⟨w, original⟩ := C.vertexForgetCuts_surjective (Set.subset_univ (C.selectedRetain S)) v
  have boundary := C.selectedCut_nonroot_copy_boundary S w (original ▸ nonroot)
  let E := C.boundaryCycleVertexEquiv (C.selectedRetain S) Q.cycle Q.closes Q.covers
  obtain ⟨i, copy⟩ := E.surjective ⟨w, boundary⟩
  have actual : C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point i) = w :=
    congrArg Subtype.val copy
  exact List.mem_ofFn.mpr ⟨i,
    (congrArg (C.vertexForgetCuts (Set.subset_univ _)) actual).trans original⟩

/-- All roots start processed; the original contour supplies every remaining vertex. -/
theorem initial_run_selectedContourSeeds_of_supported_roots :
    ((P.initialFrontier).run (C.selectedContourSeeds S Q)).processed = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  apply ((P.initialFrontier).mem_run_iff _ v).mpr
  by_cases root : v ∈ P.roots
  · exact Or.inl root
  · exact Or.inr ⟨v, C.mem_selectedContourSeeds_of_nonroot S Q v root, P.ancestor_refl v⟩

/-- The original contour history charges every nonroot exactly once, without requiring
unused isolated roots to occur on the contour. -/
theorem mem_initial_history_selectedContourSeeds_of_nonroot
    (v : {v : C.Vertex Set.univ // v ∉ P.roots}) :
    v ∈ (P.initialFrontier).history (C.selectedContourSeeds S Q) := by
  apply ((P.initialFrontier).mem_history_iff _ v).mpr
  exact ⟨v.property, v.val, C.mem_selectedContourSeeds_of_nonroot S Q v.val v.property,
    P.ancestor_refl v.val⟩

/-- Exact original contour weight accounting survives unused isolated zero-weight roots. -/
theorem sum_initial_history_selectedContourSeeds_of_zero_roots (weight : C.Vertex Set.univ → ℝ)
    (zero_roots : ∀ v ∈ P.roots, weight v = 0) :
    (((P.initialFrontier).history (C.selectedContourSeeds S Q)).map
      (fun v => weight v.val)).sum = ∑ v : C.Vertex Set.univ, weight v := by
  classical
  have distinct := (P.initialFrontier).history_nodup (C.selectedContourSeeds S Q)
  rw [← List.sum_toFinset _ distinct]
  have all : ((P.initialFrontier).history (C.selectedContourSeeds S Q)).toFinset =
      Finset.univ := by
    apply Finset.ext
    intro v
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact C.mem_initial_history_selectedContourSeeds_of_nonroot S Q v
  rw [all]
  have reindex := Finset.sum_subtype (F := inferInstance)
    (p := fun v : C.Vertex Set.univ => v ∉ P.roots)
    (Finset.univ.filter (fun v => v ∉ P.roots)) (by simp) weight
  rw [← reindex, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases root : v ∈ P.roots
  · simp only [root, not_true_eq_false, ite_false, zero_roots v root]
  · simp only [root, not_false_eq_true, ite_true]


end Unfoldings.TriangleComplex
