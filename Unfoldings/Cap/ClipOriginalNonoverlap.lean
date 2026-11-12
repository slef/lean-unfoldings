module

public import Unfoldings.Cap.ClipOriginalConforming
public import Unfoldings.Development.RefinementNonoverlap

/-! Transfer actual fine-subdivision nonoverlap to any development of the original cut cap. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.LineAlignedClip

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (L : K.LineAlignedClip Z K.originalEdgeEquations)

local instance originalNonoverlapIndexFintype : Fintype L.partition.Index :=
  @Fintype.ofFinite _ L.partition.finite

open Classical in
theorem originalDevelopment_nonoverlapping_iff (lower : Z < 0) (retain : Set C.Seam)
    [PreconnectedSpace (C.Realization retain)] (E : FacewiseDevelopment C retain)
    (A : FacewiseDevelopment L.originalComplex (L.originalRetain retain)) :
    A.Nonoverlapping ↔ E.Nonoverlapping :=
  E.refinement_nonoverlapping_iff_of_preconnected (L.originalSubdivision lower)
    (L.originalSubdivision_conforming lower retain) A

end Unfoldings.ConvexCap.LineAlignedClip
