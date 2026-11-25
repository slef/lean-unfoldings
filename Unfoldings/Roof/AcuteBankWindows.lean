module

public import Unfoldings.Roof.SharpAcuteOriginalBankHeading
public import Unfoldings.Polyhedron.ProjectedBoundaryChainInterval

/-! The uniform sharp heading budget applies to every subchain of an acute bank. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem acuteConeDevelopmentHeading_nonneg {φ : ℝ} (nonnegative : 0 ≤ φ) (small : φ ≤ π) :
    0 ≤ acuteConeDevelopmentHeading φ := by
  unfold acuteConeDevelopmentHeading shallowDevelopmentCurvature
  have sine := sin_nonneg_of_nonneg_of_le_pi nonnegative small
  have curvature := sub_nonneg.mpr (cos_le_one φ)
  have corner := arcsin_nonneg.mpr (sq_nonneg (tan (φ / 2)))
  positivity

/-- The real heading errors at any two links differ by at most the acute
budget, with the same geometric controls on the interval between them. -/
theorem abs_projectedMetricHeadingError_sub_le_sharp_of_acute_controls
    {φ : ℝ} (positive : 0 < φ) (small_tilt : φ < π / 2)
    (height_bound : (3 : ℝ) / 4 ≤ cos φ) (tilt : K.TiltBound φ)
    {retain : Set C.Seam} {m : ℕ} (full : (C.boundarySystem retain).Chain m)
    (cut : ∀ i, ¬ C.IsBoundaryEdge Set.univ (C.germEdge (full.point i).val))
    (source : Plane) (radial : (K.folding.projectedBoundaryChain full).RadialFrom source 0)
    (h k : Plane →L[ℝ] ℝ) (joint : Function.Bijective fun p => (h p, k p))
    (first : ∀ i, 0 < h ((K.folding.projectedBoundaryChain full).edge i))
    (last : ∀ i, 0 < k ((K.folding.projectedBoundaryChain full).edge i))
    (i j : Fin (m + 1)) (ordered : i ≤ j) :
    |K.projectedMetricHeadingError full i - K.projectedMetricHeadingError full j| ≤
      acuteConeDevelopmentHeading φ := by
  let P := K.folding.projectedBoundaryChain full
  by_cases equal : i = j
  · rw [equal, sub_self, abs_zero]
    exact acuteConeDevelopmentHeading_nonneg positive.le (by linarith only [small_tilt, pi_pos])
  have before : i.val < j.val := (lt_of_le_of_ne ordered equal : i < j)
  let n := j.val - i.val - 1
  have fits : i.val + (n + 1) ≤ m := by
    have bound := j.isLt
    dsimp only [n]
    omega
  let sub := full.interval i.val (n + 1) fits
  let A := K.folding.projectedBoundaryChain sub
  have geometry : A = P.interval i.val (n + 2) (by omega) :=
    K.folding.projectedBoundaryChain_interval full i.val (n + 1) fits
  have actual_radial : A.RadialFrom source 0 := by
    rw [geometry]
    intro l _
    exact radial ⟨i.val + l.val, by omega⟩ (Nat.zero_le _)
  have advance (control : Plane →L[ℝ] ℝ) (progress : ∀ l, 0 < control (P.edge l)) :
      ∀ l, 0 < control (A.edge l) := by
    intro l
    rw [geometry, PolygonalChain.interval_edge]
    exact progress _
  have estimate := K.abs_projectedMetricHeadingError_le_sharp_of_acute_controls
    positive small_tilt height_bound tilt sub (fun l => cut (full.intervalIndex i.val (n + 1) fits l))
    source actual_radial h k joint (advance h first) (advance k last)
  have phase := K.projectedMetricHeadingError_interval full i.val (n + 1) fits (Fin.last (n + 1))
  have last_eq : (⟨i.val + (Fin.last (n + 1)).val, by omega⟩ : Fin (m + 1)) = j := by
    apply Fin.ext
    change i.val + (n + 1) = j.val
    dsimp only [n]
    omega
  rw [last_eq] at phase
  exact (abs_sub_comm _ _).trans_le ((congrArg abs phase).symm.le.trans estimate)

end Unfoldings.ConvexRoof
