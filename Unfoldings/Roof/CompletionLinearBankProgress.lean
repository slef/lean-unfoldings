module

public import Unfoldings.Roof.CompletionOriginalBankWindowTrace

/-! Strict linear progress survives physical subdivision and exact endpoint trimming of a bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}
  {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

local instance completionLinearProgressIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

local notation "Old" => K.folding.projectedBoundaryChain coarse
local notation "Fine" => E.cap.projectedBoundaryChain E.originalPieceSet R.chain

open Classical in
/-- Each genuine refined edge still has the direction of its original bank. -/
theorem cap_projected_edge_progress (h : Plane →L[ℝ] ℝ)
    (progress : ∀ i, 0 < h ((Old).edge i)) (j : Fin (R.length + 1)) :
    0 < h ((Fine).edge j) := by
  obtain ⟨i, k, at_j⟩ := R.blockIndex_coverage j
  let s := R.pieceParameter i k 0
  let t := R.pieceParameter i k 1
  have first := R.block_projected_point i k 0
  have last := R.block_projected_point i k 1
  rw [at_j] at first last
  simp only [PolygonalChain.point_zero, PolygonalChain.point_one] at first last
  have direction : (Fine).edge j = ((t : ℝ) - (s : ℝ)) • (Old).edge i := by
    rw [R.cap_projectedBoundaryChain_eq, PolygonalChain.edge, first, last, PolygonalChain.edge]
    rw [PolygonalChain.point, PolygonalChain.point, AffineMap.lineMap_apply_module',
      AffineMap.lineMap_apply_module']
    change (t : ℝ) • _ + _ - ((s : ℝ) • _ + _) = _
    module
  have ordered : (s : ℝ) ≤ (t : ℝ) :=
    R.pieceParameter_monotone i k (show (0 : unitInterval) ≤ 1 from zero_le_one)
  have strict : (s : ℝ) < (t : ℝ) := by
    apply ordered.lt_of_ne
    intro equal
    have genuine := E.cap.projectedBoundaryChain_edge_ne_zero E.originalPieceSet R.chain j
    rw [direction, equal, sub_self, zero_smul] at genuine
    exact genuine rfl
  rw [direction, map_smul, smul_eq_mul]
  exact mul_pos (sub_pos.mpr strict) (progress i)

namespace TrimmedBankWindow

variable {m : ℕ} {original : (C.boundarySystem retain).Chain (m + 1)}
  {S : E.OriginalChainRefinement retain original} {a b : unitInterval}
  (W : S.TrimmedBankWindow a b)

open Classical in
/-- The exact trimmed window preserves the two independent linear directions. -/
theorem cap_projected_edge_progress (h : Plane →L[ℝ] ℝ)
    (progress : ∀ i, 0 < h ((K.folding.projectedBoundaryChain original).edge i))
    (j : Fin (W.length + 1)) :
    0 < h ((E.cap.projectedBoundaryChain E.originalPieceSet W.chain).edge j) := by
  have geometry := E.cap.projectedBoundaryChain_interval E.originalPieceSet S.chain
    W.firstIndex.val W.length W.fits
  change E.cap.projectedBoundaryChain E.originalPieceSet W.chain = _ at geometry
  rw [geometry, PolygonalChain.interval_edge]
  exact S.cap_projected_edge_progress h progress _

end TrimmedBankWindow
end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
