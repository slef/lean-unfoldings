module

public import Unfoldings.Cap.ContourRootwardOpenings
public import Unfoldings.Complex.RimStartedContour
public import Unfoldings.Geometry.CanonicalOpeningUpdate

/-! Each actual fresh contour step gives the exact complete original rootward bank opening. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

open PolygonalChain

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {P : AscendingParents (C.Vertex Set.univ)} (selection : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain selection))
  (starts : C.contourOriginalVertex selection Q 0 ∈ P.roots)

include roots starts

/-- The actual next contour source adds its own original defect at the normalized bank source.
All prior original charges and the complete tail are retained; zero defect is allowed. -/
theorem contourRootwardOpenings_source_bank (i : Fin Q.length)
    (fresh : C.contourOriginalVertex selection Q i.castSucc ∉
      (C.contourFrontier selection Q i.castSucc).processed)
    (bank : PolygonalRay ℂ
      (P.distanceToRoot (C.contourOriginalVertex selection Q i.castSucc))) :
    bank.openings (C.contourRootwardOpenings selection Q i.succ
      (C.contourOriginalVertex selection Q i.castSucc)) =
      bank.openings (⟨0, C.interiorAngularDefect Set.univ
        (C.contourOriginalVertex selection Q i.castSucc)⟩ ::
        C.contourRootwardOpenings selection Q i.castSucc
          (C.contourOriginalVertex selection Q i.castSucc)) := by
  let source := C.contourOriginalVertex selection Q i.castSucc
  let vertex := source
  let seeds := C.selectedContourSeeds selection Q
  have bound : i.val < seeds.length := by
    simp only [seeds, selectedContourSeeds, List.length_ofFn]
    omega
  have next : seeds.take (i.val + 1) = seeds.take i.val ++ [source] := by
    rw [← List.take_concat_get' seeds i.val bound]
    congr 2
    exact C.selectedContourSeeds_getElem selection Q i.castSucc
  have single : (C.contourFrontier selection Q i.castSucc).contactTime source = 1 := by
    have small := C.rim_contour_contactTime_le_one selection roots Q starts i.castSucc
    change (C.contourFrontier selection Q i.castSucc).contactTime source ≤ 1 at small
    have nonzero : (C.contourFrontier selection Q i.castSucc).contactTime source ≠ 0 := by
      intro zero
      exact fresh (((C.contourFrontier selection Q i.castSucc).contactTime_eq_zero_iff source).mp
        zero)
    omega
  unfold contourRootwardOpenings
  change bank.openings (P.historyOpenings (seeds.take (i.val + 1))
    ⟨P.root vertex, P.root_mem vertex⟩ (P.rootwardVertexPath vertex)
    (P.rootwardVertexPath_last vertex) (C.interiorAngularDefect Set.univ)) = _
  rw [next]
  exact P.historyOpenings_source_bank (seeds.take i.val)
    ⟨P.root vertex, P.root_mem vertex⟩ (P.rootwardVertexPath vertex)
    (P.rootwardVertexPath_last vertex) (C.interiorAngularDefect Set.univ)
    (P.rootwardVertexPath_ancestor vertex) source fresh single
    (by simpa only [P.rootwardVertexPath_zero] using P.ancestor_refl source) bank

end Unfoldings.TriangleComplex
