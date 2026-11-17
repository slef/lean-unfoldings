module

public import Unfoldings.Roof.CompletionOriginalBankWindow
public import Unfoldings.Cap.ProjectedBoundaryChainInterval

/-! Trimmed physical bank windows keep both literal endpoint copies and original projections. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance originalBankWindowGeometryIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain (n + 1)}
  (R : E.OriginalChainRefinement retain coarse)

open Classical in
/-- Each actual fine bank starts at its literal recorded old bank parameter. -/
theorem cap_block_projected_initial (i : Fin (n + 2)) (k : Fin ((R.block i).length + 1)) :
    (E.cap.projectedBoundaryChain E.originalPieceSet R.chain).vertex (R.blockIndex i k).castSucc =
      (K.folding.projectedBoundaryChain coarse).point i (R.blockParameter i k.castSucc) := by
  have clock : R.pieceParameter i k 0 = R.blockParameter i k.castSucc :=
    Subtype.ext (AffineMap.lineMap_apply_zero _ _)
  exact ((E.cap.projectedBoundaryChain E.originalPieceSet R.chain).point_zero
    (R.blockIndex i k)).symm.trans
    ((R.cap_block_projected_point i k 0).trans
      (congrArg ((K.folding.projectedBoundaryChain coarse).point i) clock))

namespace TrimmedBankWindow

variable {R} {a b : unitInterval} (W : R.TrimmedBankWindow a b)

open Classical in
/-- The far endpoint is the same actual cut-vertex copy as the excluded next bank's start. -/
theorem finish_vertex :
    E.originalComplex.boundaryEndVertex (E.originalRetain retain)
      (E.originalComplex.boundaryTurn (E.originalRetain retain) W.chain.last) =
    E.originalComplex.boundaryEndVertex (E.originalRetain retain)
      (R.chain.point W.lastIndex) := by
  have order := W.ordered
  change W.firstIndex.val < W.lastIndex.val at order
  let old : Fin R.length := ⟨W.lastIndex.val - 1, by
    have bound := W.lastIndex.isLt
    omega⟩
  have next_index : old.succ = W.lastIndex := by
    apply Fin.ext
    change W.lastIndex.val - 1 + 1 = W.lastIndex.val
    omega
  have last_name : W.chain.last = R.chain.point old.castSucc :=
    (R.chain.interval_last W.firstIndex.val W.length W.fits).trans
      (congrArg R.chain.point (Fin.ext (by
        change W.firstIndex.val + W.length = W.lastIndex.val - 1
        dsimp only [length]
        omega)))
  have vertex := (E.originalComplex.boundaryMate_spec (E.originalRetain retain)
    (E.originalComplex.boundaryTurn (E.originalRetain retain)
      (R.chain.point old.castSucc))).2.symm.trans
      (congrArg (E.originalComplex.boundaryEndVertex (E.originalRetain retain))
        ((R.chain.next old).trans (congrArg R.chain.point next_index)))
  exact (congrArg (fun p => E.originalComplex.boundaryEndVertex (E.originalRetain retain)
    (E.originalComplex.boundaryTurn (E.originalRetain retain) p)) last_name).trans vertex

open Classical in
/-- The actual physical window starts at the original geometric first trim. -/
theorem cap_projected_initial :
    (E.cap.projectedBoundaryChain E.originalPieceSet W.chain).vertex 0 =
      (K.folding.projectedBoundaryChain coarse).point 0 a := by
  let F := E.cap.folding.restrictFaces E.originalPieceSet
  exact (E.cap.projectedBoundaryChain_vertex_castSucc E.originalPieceSet W.chain 0).trans
    ((congrArg (fun p => Cap.horizontal (F.boundaryPosition p)) W.first).trans
      ((E.cap.projectedBoundaryChain_vertex_castSucc E.originalPieceSet R.chain
        W.firstIndex).symm.trans
        ((R.cap_block_projected_initial 0 W.firstPiece).trans
          (congrArg ((K.folding.projectedBoundaryChain coarse).point 0) W.first_time))))

open Classical in
/-- The true terminal physical endpoint is the original geometric last trim. -/
theorem cap_projected_terminal :
    (E.cap.projectedBoundaryChain E.originalPieceSet W.chain).vertex (Fin.last (W.length + 1)) =
      (K.folding.projectedBoundaryChain coarse).point (Fin.last (n + 1)) b := by
  let F := E.cap.folding.restrictFaces E.originalPieceSet
  have same := congrArg (fun v => Cap.horizontal (F.toSpace (E.originalRetain retain)
    (E.originalComplex.vertexPoint (E.originalRetain retain) v))) W.finish_vertex
  exact (E.cap.projectedBoundaryChain_vertex_last E.originalPieceSet W.chain).trans
    (same.trans ((E.cap.projectedBoundaryChain_vertex_castSucc E.originalPieceSet R.chain
      W.lastIndex).symm.trans
        ((R.cap_block_projected_initial (Fin.last (n + 1)) W.lastPiece).trans
          (congrArg ((K.folding.projectedBoundaryChain coarse).point (Fin.last (n + 1)))
            W.last_time))))

end TrimmedBankWindow
end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
