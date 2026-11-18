module

public import Unfoldings.Cap.ProcessedBankOpeningHistory
public import Unfoldings.Complex.SelectedContourNeighbors
public import Unfoldings.Topology.ParentOrbitPath

/-! Construct the original rootward opening history at every actual contour stage. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (selection : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain selection)) (stage : Fin (Q.length + 1))

/-- Actual contour-prefix charges on the original rootward path, omitting all flat events. -/
def contourRootwardOpenings (vertex : C.Vertex Set.univ) :
    List (PolygonalChain.Opening (P.distanceToRoot vertex)) :=
  P.historyOpenings ((C.selectedContourSeeds selection Q).take stage.val)
    ⟨P.root vertex, P.root_mem vertex⟩ (P.rootwardVertexPath vertex)
    (P.rootwardVertexPath_last vertex) (C.interiorAngularDefect Set.univ)

end Unfoldings.TriangleComplex

namespace Unfoldings.ConvexCap

open PolygonalChain

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (selection : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain selection)) (stage : Fin (Q.length + 1))
  (vertex : C.Vertex Set.univ)

/-- Every original rootward bank has its exact measured current phase; all path data is derived. -/
theorem contourRootwardOpenings_heading
    (processed : vertex ∈ (C.contourFrontier selection Q stage).processed)
    (i : Fin (P.distanceToRoot vertex)) :
    openingHeading (C.contourRootwardOpenings selection Q stage vertex) i =
      K.processedParentBankHeading selection roots (C.contourFrontier selection Q stage)
        (P.rootwardVertexPath vertex i.castSucc) (P.rootwardVertexPath_nonroot vertex i)
        (P.rootwardVertexPath_processed vertex (C.contourFrontier selection Q stage)
          processed i.castSucc) := by
  unfold TriangleComplex.contourRootwardOpenings
  rw [P.historyOpenings_heading _ _ _ _ _ (P.rootwardVertexPath_ancestor vertex)]
  exact (K.processedParentBankHeading_eq selection roots (C.contourFrontier selection Q stage)
    (P.rootwardVertexPath vertex i.castSucc) _ _).symm

include K in
/-- The actual contour and rootward path spend at most total original curvature. -/
theorem contourRootwardOpenings_budget_le :
    openingBudget (C.contourRootwardOpenings selection Q stage vertex) ≤
      C.totalInteriorAngularDefect Set.univ :=
  P.historyOpenings_budget_le_total _ _ _ _ _ K.interiorCurvature_nonneg

include K in
/-- Every constructed contour event is positive, even with flat original vertices. -/
theorem contourRootwardOpenings_positive (event : Opening (P.distanceToRoot vertex))
    (member : event ∈ C.contourRootwardOpenings selection Q stage vertex) : 0 < event.angle :=
  P.historyOpenings_positive _ _ _ _ _ K.interiorCurvature_nonneg event member

end Unfoldings.ConvexCap
