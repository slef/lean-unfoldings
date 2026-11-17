module

public import Unfoldings.Roof.CompletionChainProjectedParameters
public import Unfoldings.Cap.ProjectedBankVertexParameters
public import Unfoldings.Geometry.FiniteInterpolation

/-! Actual marked cap vertices occur at exact original bank parameters in the fine chain. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance completionBankVertexParametersIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

open Classical in
/-- The actual comparison cap retains every fine bank's exact old projected parameter. -/
theorem cap_block_projected_point (i : Fin (n + 1)) (k : Fin ((R.block i).length + 1))
    (t : unitInterval) :
    (E.cap.projectedBoundaryChain E.originalPieceSet R.chain).point (R.blockIndex i k) t =
      (K.folding.projectedBoundaryChain coarse).point i (R.pieceParameter i k t) :=
  (congrArg (fun P : PolygonalChain Plane (R.length + 1) => P.point (R.blockIndex i k) t)
    R.cap_projectedBoundaryChain_eq).trans (R.block_projected_point i k t)

open Classical in
/-- A global physical mesh vertex on an old bank has an exact recorded fine-vertex time.
Neither the fine index nor a proposed ordering of a marked trim is assumed. -/
theorem exists_block_parameter_of_cap_vertex (i : Fin (n + 1)) (a : unitInterval)
    (v : E.partition.pairedComplex.Vertex Set.univ)
    (same : (K.folding.projectedBoundaryChain coarse).point i a = E.cap.projectedVertex v) :
    ∃ k : Fin ((R.block i).length + 2), R.blockParameter i k = a := by
  obtain ⟨k, t, at_a⟩ := exists_finite_interpolation (R.blockParameter i)
    (R.blockParameter_zero i) (R.blockParameter_last i) a
  have clock : R.pieceParameter i k t = a := Subtype.ext at_a
  have projected := (R.cap_block_projected_point i k t).trans
    ((congrArg ((K.folding.projectedBoundaryChain coarse).point i) clock).trans same)
  rcases E.cap.projectedBoundaryChain_parameter_endpoint_of_vertex E.originalPieceSet R.chain
      (R.blockIndex i k) t v projected with rfl | rfl
  · refine ⟨k.castSucc, Subtype.ext ?_⟩
    simpa only [Set.Icc.coe_zero, AffineMap.lineMap_apply_zero] using at_a
  · refine ⟨k.succ, Subtype.ext ?_⟩
    simpa only [Set.Icc.coe_one, AffineMap.lineMap_apply_one] using at_a

open Classical in
/-- A marked point before the old far endpoint starts an actual fine bank.
This is the index needed to extract a trimmed interval of the original bank chain. -/
theorem exists_block_start_parameter_of_cap_vertex (i : Fin (n + 1)) (a : unitInterval)
    (before : a.val < 1) (v : E.partition.pairedComplex.Vertex Set.univ)
    (same : (K.folding.projectedBoundaryChain coarse).point i a = E.cap.projectedVertex v) :
    ∃ k : Fin ((R.block i).length + 1), R.blockParameter i k.castSucc = a := by
  obtain ⟨k, at_a⟩ := R.exists_block_parameter_of_cap_vertex i a v same
  have bound : k.val < (R.block i).length + 1 := by
    by_contra absent
    have last : k = Fin.last ((R.block i).length + 1) :=
      Fin.ext (by
        change k.val = (R.block i).length + 1
        have upper := k.isLt
        omega)
    rw [last, R.blockParameter_last] at at_a
    have values := congrArg Subtype.val at_a
    change 1 = a.val at values
    linarith
  exact ⟨⟨k.val, bound⟩, at_a⟩

open Classical in
/-- Every fine piece in an earlier old bank precedes every piece in a later old bank. -/
theorem blockIndex_lt_of_block_lt {i j : Fin (n + 1)} (earlier : i < j)
    (k : Fin ((R.block i).length + 1)) (l : Fin ((R.block j).length + 1)) :
    R.blockIndex i k < R.blockIndex j l := by
  let h : Fin n := ⟨i.val, by have bound := j.isLt; change i.val < j.val at earlier; omega⟩
  have at_i : h.castSucc = i := Fin.ext rfl
  have next := R.coarseIndex_succ h
  rw [at_i] at next
  have old_order : h.succ ≤ j := by
    change i.val + 1 ≤ j.val
    exact earlier
  have coarse_order := R.coarseIndex_strictMono.monotone old_order
  have left := R.blockIndex_val i k
  have right := R.blockIndex_val j l
  change (R.blockIndex i k).val < (R.blockIndex j l).val
  change (R.coarseIndex h.succ).val ≤ (R.coarseIndex j).val at coarse_order
  have inside := k.isLt
  omega

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
