module

public import Unfoldings.Complex.PairedBankComponents

/-!
# Boundary components descend across forest cuts

At an uncut vertex, restoring a retained seam changes no vertex copy; restoring
an actual cut seam joins two copies already in the same boundary component.
The finite germ chains therefore make boundary-component labels well-defined
on the original vertex classes. Interior copies receive the separate `none`
label, rather than an arbitrary boundary component.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam)

def vertexBoundaryComponent (v : C.Vertex retain) :
    Option (C.boundaryGraph retain).adjacencyGraph.ConnectedComponent := by
  classical
  exact if h : C.IsBoundaryVertex retain v then
    some ((C.boundaryGraph retain).adjacencyGraph.connectedComponentMk ⟨v, h⟩) else none

@[simp] theorem vertexBoundaryComponent_boundary (v : C.BoundaryVertex retain) :
    C.vertexBoundaryComponent retain v.val =
      some ((C.boundaryGraph retain).adjacencyGraph.connectedComponentMk v) := by
  simp only [vertexBoundaryComponent, dite_eq_left v.property]

theorem vertexBoundaryComponent_eq_of_reaches {p q : C.BoundaryVertex retain}
    (reachable : (C.boundaryGraph retain).graph.Reaches p q) :
    C.vertexBoundaryComponent retain p.val = C.vertexBoundaryComponent retain q.val := by
  rw [C.vertexBoundaryComponent_boundary, C.vertexBoundaryComponent_boundary]
  exact congrArg some (SimpleGraph.ConnectedComponent.eq.mpr
    ((C.boundaryGraph retain).graph_reaches_iff_adjacency.mp reachable))

variable (closed : ∀ e, ¬ C.IsBoundaryEdge Set.univ e)
  (forest : (C.cutSeamGraph retain).IsAcyclic)

include closed forest in
theorem vertexBoundaryComponent_eq_of_crossing {p q : C.Germ}
    (crossing : C.GermCrosses Set.univ p q) :
    C.vertexBoundaryComponent retain (C.vertexOfCorner retain p.1) =
      C.vertexBoundaryComponent retain (C.vertexOfCorner retain q.1) := by
  obtain ⟨s, _kept, side, b, rfl, rfl⟩ := crossing
  by_cases kept : s ∈ retain
  · exact congrArg (C.vertexBoundaryComponent retain)
      (show C.GermCrosses retain
        (C.germOfEndpoint (C.seamSide s side) b)
        (C.germOfEndpoint (C.seamSide s (!side)) (C.acrossEndpoint s side b))
        from ⟨s, kept, side, b, rfl, rfl⟩).vertex_eq
  · let cut : C.CutSeam retain := ⟨s, kept⟩
    let first := (C.boundaryEndEquiv retain).symm (C.cutBank retain cut side, b)
    let second := (C.boundaryEndEquiv retain).symm
      (C.cutBank retain cut (!side), C.acrossEndpoint s side b)
    have same_seam : C.bankCutSeam retain closed (C.boundaryEndEquiv retain first).1 =
        C.bankCutSeam retain closed (C.boundaryEndEquiv retain second).1 := by
      simp only [first, second, Equiv.apply_symm_apply, C.bankCutSeam_cutBank]
    exact C.vertexBoundaryComponent_eq_of_reaches retain
      (C.boundaryEnds_reaches_of_same_cutSeam retain closed forest first second same_seam)

include closed forest in
theorem vertexBoundaryComponent_eq_of_germStep {p q : C.Germ}
    (step : C.GermStep Set.univ p q) :
    C.vertexBoundaryComponent retain (C.vertexOfCorner retain p.1) =
      C.vertexBoundaryComponent retain (C.vertexOfCorner retain q.1) := by
  rcases step with rfl | rfl
  · rfl
  · obtain ⟨q, crossing⟩ := (C.exists_germCrosses_iff Set.univ p).mpr (closed (C.germEdge p))
    rw [C.mateGerm_of_crossing crossing]
    exact C.vertexBoundaryComponent_eq_of_crossing retain closed forest crossing

include closed forest in
theorem vertexBoundaryComponent_eq_of_germs_related {p q : C.Germ}
    (related : Relation.EqvGen (C.GermStep Set.univ) p q) :
    C.vertexBoundaryComponent retain (C.vertexOfCorner retain p.1) =
      C.vertexBoundaryComponent retain (C.vertexOfCorner retain q.1) := by
  induction related with
  | rel p q step => exact C.vertexBoundaryComponent_eq_of_germStep retain closed forest step
  | refl p => rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def originalVertexBoundaryComponent (v : C.Vertex Set.univ) :
    Option (C.boundaryGraph retain).adjacencyGraph.ConnectedComponent :=
  Quotient.lift (fun c => C.vertexBoundaryComponent retain (C.vertexOfCorner retain c))
    (fun c d related => C.vertexBoundaryComponent_eq_of_germs_related retain closed forest
      ((C.germs_related_iff_vertex_eq Set.univ (c, false) (d, false)).mpr
        ((C.vertexOfCorner_eq_iff Set.univ c d).mpr related))) v

@[simp] theorem originalVertexBoundaryComponent_forget (v : C.Vertex retain) :
    C.originalVertexBoundaryComponent retain closed forest
        (C.vertexForgetCuts (Set.subset_univ retain) v) = C.vertexBoundaryComponent retain v := by
  obtain ⟨c, rfl⟩ := C.vertexOfCorner_surjective retain v
  rfl

end Unfoldings.TriangleComplex
