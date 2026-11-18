module

public import Unfoldings.Roof.CompletionProjectedChainFans
public import Unfoldings.Complex.AffineProjectionChains
public import Unfoldings.Complex.BoundaryChainHeadingStep

/-! Every real projected heading prefix survives actual physical bank subdivision. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance completionProjectedChainHeadingIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain n}
  (R : E.OriginalChainRefinement retain coarse)

open Classical in
def projectedChain : (E.originalProjectedComplex.boundarySystem
    (E.originalRetain retain)).Chain R.length :=
  E.originalComplex.affineProjectionChain E.originalProjection E.originalProjection_joined R.chain

open Classical in
@[simp] theorem projectedChain_point (i : Fin (R.length + 1)) :
    R.projectedChain.point i = E.originalComplex.affineProjectionBoundaryEndEquiv
      E.originalProjection E.originalProjection_joined (E.originalRetain retain)
      (R.chain.point i) := rfl

open Classical in
def projectedHeading : Fin (R.length + 1) → ℝ :=
  E.originalProjectedComplex.boundaryChainRollHeading R.projectedChain

open Classical in
theorem block_projected_heading (i : Fin (n + 1)) (k : Fin ((R.block i).length + 1)) :
    R.projectedHeading (R.blockIndex i k) = R.projectedHeading (R.coarseIndex i) := by
  induction k using Fin.induction with
  | zero => rw [R.blockIndex_zero]
  | succ k previous =>
    have next : (R.blockIndex i k.succ).val = (R.blockIndex i k.castSucc).val + 1 := by
      rw [R.blockIndex_val, R.blockIndex_val]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have step := E.originalProjectedComplex.boundaryChainRollHeading_step_of_indices
      R.projectedChain next
    have flat : E.originalProjectedComplex.totalAngle (E.originalRetain retain)
        (E.originalProjectedComplex.boundaryEndVertex (E.originalRetain retain)
          (R.projectedChain.point (R.blockIndex i k.succ))) = Real.pi := by
      have same := congrArg (fun p : E.originalComplex.BoundaryEnd (E.originalRetain retain) =>
        E.originalProjectedComplex.totalAngle (E.originalRetain retain)
          (E.originalComplex.affineProjectionVertexEquiv E.originalProjection
            E.originalProjection_joined (E.originalRetain retain)
            (E.originalComplex.boundaryEndVertex (E.originalRetain retain) p)))
        (R.blockIndex_point i k.succ)
      exact same.trans (R.block_projected_totalAngle_eq_pi i k)
    exact step.trans ((congrArg₂ (fun a b : ℝ => a + b) previous
      (congrArg (fun a : ℝ => Real.pi - a) flat)).trans (by simp only [sub_self, add_zero]))

open Classical in
/-- Original hinges retain their exact real projected heading, including full revolutions. -/
theorem coarseIndex_projected_heading (i : Fin (n + 1)) :
    R.projectedHeading (R.coarseIndex i) = K.projectedMetricHeading coarse i := by
  induction i using Fin.induction with
  | zero => rw [R.coarseIndex_zero]; rfl
  | succ k previous =>
    have next : (R.coarseIndex k.succ).val =
        (R.blockIndex k.castSucc (Fin.last (R.block k.castSucc).length)).val + 1 := by
      rw [R.coarseIndex_succ, R.blockIndex_val, Fin.val_last]
    have step := E.originalProjectedComplex.boundaryChainRollHeading_step_of_indices
      R.projectedChain next
    have angle : E.originalProjectedComplex.totalAngle (E.originalRetain retain)
        (E.originalProjectedComplex.boundaryEndVertex (E.originalRetain retain)
          (R.projectedChain.point (R.coarseIndex k.succ))) =
        K.projectedTotalAngle retain (C.boundaryEndVertex retain (coarse.point k.succ)) :=
      E.original_projectedTotalAngle_eq retain _ _ (R.coarseIndex_image k.succ)
    have earlier := (R.block_projected_heading k.castSucc
      (Fin.last (R.block k.castSucc).length)).trans previous
    have updated := step.trans (congrArg₂ (fun a b : ℝ => a + b) earlier
      (congrArg (fun a : ℝ => Real.pi - a) angle))
    have formula := Fin.partialSum_succ (fun j : Fin n => Real.pi -
      K.projectedTotalAngle retain (C.boundaryEndVertex retain (coarse.point j.succ))) k
    exact updated.trans ((K.projectedMetricHeading_eq coarse k.succ).trans
      (formula.trans (congrArg (fun a => a + (Real.pi - K.projectedTotalAngle retain
        (C.boundaryEndVertex retain (coarse.point k.succ))))
        (K.projectedMetricHeading_eq coarse k.castSucc).symm))).symm

open Classical in
/-- Every actual fine bank piece has the exact unreduced heading of its old projected bank. -/
theorem block_projected_heading_eq_coarse (i : Fin (n + 1))
    (k : Fin ((R.block i).length + 1)) :
    R.projectedHeading (R.blockIndex i k) = K.projectedMetricHeading coarse i :=
  (R.block_projected_heading i k).trans (R.coarseIndex_projected_heading i)

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement
