module

public import Unfoldings.Roof.CompletionProjectedCapHeading
public import Unfoldings.Roof.CompletionOriginalBankWindow

/-! The actual comparison cap retains the original real projected heading across every trim. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement.TrimmedBankWindow

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {φ : ℝ} {region : Set Plane}
  {E : K.CompletionMesh φ region K.originalEdgeEquations}

local instance completionProjectedBankWindowIndexFintype : Fintype E.partition.Index :=
  @Fintype.ofFinite _ E.partition.finite

variable {retain : Set C.Seam} {n : ℕ} {coarse : (C.boundarySystem retain).Chain (n + 1)}
  {R : E.OriginalChainRefinement retain coarse} {a b : unitInterval} (W : R.TrimmedBankWindow a b)

open Classical in
/-- Trimming preserves the exact original projected terminal heading, without reduction modulo π. -/
theorem terminal_projected_heading_eq (positive : 0 < b.val) :
    E.cap.projectedFanRollHeading E.originalPieceSet W.chain (Fin.last W.length) =
      K.projectedMetricHeading coarse (Fin.last (n + 1)) := by
  have formula : E.originalProjectedComplex.boundaryChainRollHeading
      (E.originalComplex.affineProjectionChain E.originalProjection
        E.originalProjection_joined W.chain) (Fin.last W.length) =
      R.projectedHeading
          (R.chain.intervalIndex W.firstIndex.val W.length W.fits (Fin.last W.length)) -
        R.projectedHeading (R.chain.intervalIndex W.firstIndex.val W.length W.fits 0) :=
    E.originalProjectedComplex.boundaryChainRollHeading_interval R.projectedChain
      W.firstIndex.val W.length W.fits (Fin.last W.length)
  have indices := congrArg₂ (fun i j => R.projectedHeading i - R.projectedHeading j)
    (W.interval_last_index positive) W.interval_first_index
  have start : R.projectedHeading W.firstIndex = 0 := R.block_projected_heading_eq_coarse
    0 W.firstPiece
  have finish := R.block_projected_heading_eq_coarse (Fin.last (n + 1))
    (W.previousPiece positive)
  exact (E.cap_projectedFanRollHeading_eq W.chain (Fin.last W.length)).trans
    (formula.trans (indices.trans ((congrArg₂ (fun x y : ℝ => x - y) finish start).trans
      (sub_zero _))))

open Classical in
/-- The actual physical comparison error is the original untrimmed real bank error. -/
theorem terminal_real_error_eq (positive : 0 < b.val) :
    E.originalComplex.boundaryChainRollHeading W.chain (Fin.last W.length) -
        E.cap.projectedFanRollHeading E.originalPieceSet W.chain (Fin.last W.length) =
      K.projectedMetricHeadingError coarse (Fin.last (n + 1)) :=
  congrArg₂ (fun x y : ℝ => x - y) (W.terminal_heading_eq positive)
    (W.terminal_projected_heading_eq positive)

end Unfoldings.ConvexRoof.CompletionMesh.OriginalChainRefinement.TrimmedBankWindow
