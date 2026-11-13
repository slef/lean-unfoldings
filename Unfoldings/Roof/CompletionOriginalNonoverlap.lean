module

public import Unfoldings.Roof.CompletionOriginalConforming
public import Unfoldings.Development.RefinementNonoverlap

/-! Transfer actual fine-subdivision nonoverlap to any development of the original cut roof. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  (L : K.CompletionMesh φ region K.originalEdgeEquations)

local instance originalNonoverlapIndexFintype : Fintype L.partition.Index :=
  @Fintype.ofFinite _ L.partition.finite

open Classical in
theorem originalDevelopment_nonoverlapping_iff (retain : Set C.Seam)
    [PreconnectedSpace (C.Realization retain)] (E : FacewiseDevelopment C retain)
    (A : FacewiseDevelopment L.originalComplex (L.originalRetain retain)) :
    A.Nonoverlapping ↔ E.Nonoverlapping :=
  E.refinement_nonoverlapping_iff_of_preconnected (L.originalSubdivision)
    (L.originalSubdivision_conforming retain) A

end Unfoldings.ConvexRoof.CompletionMesh
