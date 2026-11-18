module

public import Unfoldings.Cap.ContourRootwardOpeningUpdate

/-! The next actual source and its prior contour history spend original curvature only once. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

open PolygonalChain

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {P : AscendingParents (C.Vertex Set.univ)} (selection : P.EdgeSelection C.seamGraph)
  (Q : C.BoundaryContour (C.selectedRetain selection)) (i : Fin Q.length)

include K in
/-- The source-first gap word has the original total-curvature bound, with no charge certificate. -/
theorem contour_source_opening_budget_le
    (fresh : C.contourOriginalVertex selection Q i.castSucc ∉
      (C.contourFrontier selection Q i.castSucc).processed) :
    openingBudget (⟨0, C.interiorAngularDefect Set.univ
      (C.contourOriginalVertex selection Q i.castSucc)⟩ ::
      C.contourRootwardOpenings selection Q i.castSucc
        (C.contourOriginalVertex selection Q i.castSucc)) ≤
      C.totalInteriorAngularDefect Set.univ := by
  classical
  let source := C.contourOriginalVertex selection Q i.castSucc
  let seeds := (C.selectedContourSeeds selection Q).take i.val
  let root : {v // v ∈ P.roots} := ⟨P.root source, P.root_mem source⟩
  let names := P.historySources seeds root
  have distinct : (source :: names).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, P.historySources_nodup seeds root⟩
    intro present
    have processed := (P.mem_historySources seeds root source).mp present
    exact fresh ((AscendingParents.ParentFrontier.mem_processedDescendants _ _ _).mp processed).1
  have old_budget : openingBudget (C.contourRootwardOpenings selection Q i.castSucc source) =
      (names.map (C.interiorAngularDefect Set.univ)).sum := by
    unfold TriangleComplex.contourRootwardOpenings AscendingParents.historyOpenings
    rw [withoutZeroOpenings_budget, P.ancestorOpenings_budget]
    simp only [abs_of_nonneg (K.interiorCurvature_nonneg _)]
    rfl
  calc
    _ = ((source :: names).map (C.interiorAngularDefect Set.univ)).sum := by
      change |C.interiorAngularDefect Set.univ source| +
        openingBudget (C.contourRootwardOpenings selection Q i.castSucc source) = _
      rw [abs_of_nonneg (K.interiorCurvature_nonneg source), old_budget]
      rfl
    _ = ∑ v ∈ (source :: names).toFinset, C.interiorAngularDefect Set.univ v :=
      (List.sum_toFinset _ distinct).symm
    _ ≤ C.totalInteriorAngularDefect Set.univ :=
      K.sum_interiorAngularDefect_le_totalCurvature _

end Unfoldings.ConvexCap
