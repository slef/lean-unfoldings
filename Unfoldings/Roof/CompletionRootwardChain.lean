module

public import Unfoldings.Roof.CompletionChainRadial
public import Unfoldings.Complex.RootwardReferenceChain

/-! Concrete physical fine refinements of the current surviving rootward parent banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (E : K.CompletionMesh φ region K.originalEdgeEquations)

local instance completionRootwardIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)
  (i : Fin (Q.length + 1))
  (single : (C.contourFrontier S Q i).contactTime (C.contourOriginalVertex S Q i) = 1)
  (m : ℕ) (length : P.distanceToRoot (C.contourOriginalVertex S Q i) = m + 2)

open Classical in
/-- Construct the entire physical surviving rootward stem. Every bank is an actual original
parent bank; refinement, fans, lengths, headings and endpoint copies are all derived. -/
def rootwardChainRefinement :
    E.OriginalChainRefinement (C.processedParentRetain S (C.contourFrontier S Q i))
      (K.folding.rootwardParentBankChain S roots Q starts i single m length) :=
  E.originalChainRefinement _ _ (fun k =>
    (SpatialFolding.rootwardParentBank S roots Q starts i single m length k).property.2.2)

variable (fresh : C.contourOriginalVertex S Q i ∉ (C.contourFrontier S Q i).processed)

open Classical in
/-- The complete physical fine stem has exactly the original ancestor-reference roll image.
This is a refinement of the original cut space; transport through inserted gaps is separate. -/
theorem rootwardChainRefinement_reference_roll_trace :
    Set.range (E.originalComplex.boundaryChainRoll
      (E.rootwardChainRefinement S roots Q starts i single m length).chain).path =
    Set.range (C.boundaryChainRoll
      (K.folding.rootwardReferenceBankChain S roots Q starts i fresh single m length)).path := by
  rw [K.folding.rootwardReferenceBankChain_roll]
  exact (E.rootwardChainRefinement S roots Q starts i single m length).roll_path_range_eq

open Classical in
/-- Refining the actual current stem preserves radial order of the original ancestor reference. -/
theorem rootwardChainRefinement_reference_radial (source : ℂ)
    (radial : (C.boundaryChainRoll
      (K.folding.rootwardReferenceBankChain S roots Q starts i fresh single m length)).RadialFrom
        source 0) :
    (E.originalComplex.boundaryChainRoll
      (E.rootwardChainRefinement S roots Q starts i single m length).chain).RadialFrom
        source 0 := by
  apply (E.rootwardChainRefinement S roots Q starts i single m length).roll_radialFrom source
  rw [← K.folding.rootwardReferenceBankChain_roll S roots Q starts i fresh single m length]
  exact radial

open Classical in
/-- The physical fine stem has the full intrinsic arclength of the original path reference. -/
theorem rootwardChainRefinement_reference_length :
    (E.originalComplex.boundaryChainRoll
      (E.rootwardChainRefinement S roots Q starts i single m length).chain).projectedLength =
    (C.boundaryChainRoll
      (K.folding.rootwardReferenceBankChain S roots Q starts i
        fresh single m length)).projectedLength :=
  (E.rootwardChainRefinement S roots Q starts i single m length).roll_length_eq.trans
    (congrArg PolygonalChain.projectedLength
      (K.folding.rootwardReferenceBankChain_roll S roots Q starts i fresh single m length)).symm

end Unfoldings.ConvexRoof.CompletionMesh
