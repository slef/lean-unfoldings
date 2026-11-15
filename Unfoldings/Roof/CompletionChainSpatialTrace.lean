module

public import Unfoldings.Roof.CompletionChainTrace
public import Unfoldings.Roof.CompletionOriginalSpatial

/-! Complete physical spatial bank traces agree with their original paths. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance completionSpatialTraceIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

open Classical in
/-- All points of the physical fine banks, including every endpoint, have exactly
those original folded positions. This uses the concrete physical folding. -/
theorem spatial_trace_image :
    (E.partition.pairedFolding.restrictFaces E.originalPieceSet).toSpace
        (E.originalRetain retain) '' E.originalComplex.boundaryChainTrace R.chain =
      K.folding.toSpace retain '' C.boundaryChainTrace coarse := by
  have maps : (E.partition.pairedFolding.restrictFaces E.originalPieceSet).toSpace
      (E.originalRetain retain) = K.folding.toSpace retain ∘ E.originalMetricEquiv retain := by
    funext x
    exact E.originalMetricEquiv_toSpace retain x
  rw [maps]
  exact R.observed_trace_image (K.folding.toSpace retain)

open Classical in
/-- Horizontal projection of the entire physical fine trace equals the original one. -/
theorem projected_trace_image :
    (Cap.horizontal ∘ (E.partition.pairedFolding.restrictFaces E.originalPieceSet).toSpace
        (E.originalRetain retain)) '' E.originalComplex.boundaryChainTrace R.chain =
      (Cap.horizontal ∘ K.folding.toSpace retain) '' C.boundaryChainTrace coarse := by
  ext p
  constructor
  · rintro ⟨x, member, at_p⟩
    obtain ⟨y, old_member, same⟩ := R.spatial_trace_image.subset ⟨x, member, rfl⟩
    exact ⟨y, old_member, (congrArg Cap.horizontal same).trans at_p⟩
  · rintro ⟨y, member, at_p⟩
    obtain ⟨x, fine_member, same⟩ := R.spatial_trace_image.symm.subset ⟨y, member, rfl⟩
    exact ⟨x, fine_member, (congrArg Cap.horizontal same).trans at_p⟩

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
