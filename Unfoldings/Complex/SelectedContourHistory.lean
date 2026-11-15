module

public import Unfoldings.Complex.BoundaryContour
public import Unfoldings.Complex.SelectedIncidence
public import Unfoldings.Complex.Curvature
public import Unfoldings.Topology.ParentFrontierReach

/-! Actual original cut contours construct complete first-contact parent processing histories. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))

/-- Use the original named cut copies in their actual cyclic bank order as processing seeds.
Original vertices may repeat; the constructed first-contact history removes old ancestors. -/
def selectedContourSeeds : List (C.Vertex Set.univ) :=
  List.ofFn (fun i : Fin (Q.length + 1) => C.vertexForgetCuts (Set.subset_univ _)
    (C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point i)))

include roots in
/-- The actual contour supplies every original vertex, without a separate path-cover premise. -/
theorem mem_selectedContourSeeds (v : C.Vertex Set.univ) : v ∈ C.selectedContourSeeds S Q := by
  obtain ⟨w, original⟩ := C.vertexForgetCuts_surjective (Set.subset_univ (C.selectedRetain S)) v
  let E := C.boundaryCycleAllVertexEquiv (C.selectedRetain S) Q.cycle Q.closes Q.covers
    (C.selectedCut_all_vertices_boundary S roots)
  obtain ⟨i, copy⟩ := E.surjective w
  have actual : C.boundaryEndVertex (C.selectedRetain S) (Q.cycle.point i) = w := copy
  apply List.mem_ofFn.mpr
  exact ⟨i, (congrArg (C.vertexForgetCuts (Set.subset_univ _)) actual).trans original⟩

include roots in
/-- Processing the original actual contour explores the entire parent forest. -/
theorem initial_run_selectedContourSeeds :
    ((P.initialFrontier).run (C.selectedContourSeeds S Q)).processed = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  apply ((P.initialFrontier).mem_run_iff _ v).mpr
  exact Or.inr ⟨v, C.mem_selectedContourSeeds S roots Q v, P.ancestor_refl v⟩

include roots in
/-- Every original nonroot is charged by the actual contour's constructed first-contact
history. Distinctness follows independently from `ParentFrontier.history_nodup`. -/
theorem mem_initial_history_selectedContourSeeds (v : {v : C.Vertex Set.univ // v ∉ P.roots}) :
    v ∈ (P.initialFrontier).history (C.selectedContourSeeds S Q) := by
  apply ((P.initialFrontier).mem_history_iff _ v).mpr
  exact ⟨v.property, v.val, C.mem_selectedContourSeeds S roots Q v.val, P.ancestor_refl v.val⟩

include roots in
/-- The actual contour history preserves every original weight exactly once off the roots. -/
theorem sum_initial_history_selectedContourSeeds (weight : C.Vertex Set.univ → ℝ)
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
    exact C.mem_initial_history_selectedContourSeeds S roots Q v
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

include roots in
/-- The actual original contour's first-contact schedule charges exactly total original
interior curvature, even when the cap is flat or some original vertices have zero defect. -/
theorem sum_initial_history_curvature :
    (((P.initialFrontier).history (C.selectedContourSeeds S Q)).map
      (fun v => C.interiorAngularDefect Set.univ v.val)).sum =
        C.totalInteriorAngularDefect Set.univ := by
  apply C.sum_initial_history_selectedContourSeeds S roots Q
  intro v root
  rw [roots] at root
  change C.IsBoundaryVertex Set.univ v at root
  simp only [interiorAngularDefect, ite_eq_left root]

end Unfoldings.TriangleComplex
