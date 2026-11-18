module

public import Unfoldings.Roof.SupportedBankWindowErrors
public import Unfoldings.Geometry.PlanePolarWindow

/-! Physical cap comparisons give the exact local polar-window hypothesis for weighted rolling. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} {K : ConvexRoof C}
  {φ η : ℝ} {retain : Set C.Seam} {m : ℕ} {full : (C.boundarySystem retain).Chain m}
  {control : Plane}

open Classical in
/-- Actual comparisons bound the original real phase on every short polar window in any frame. -/
theorem SupportedBankWindowComparisons.polar_error
    (comparisons : K.SupportedBankWindowComparisons φ η retain full control)
    (nonnegative : 0 ≤ η) (L : Plane ≃ₗᵢ[ℝ] ℂ)
    (genuine : ∀ i, (K.folding.projectedBoundaryChain full).vertex i - control ≠ 0)
    (i j : Fin (m + 1)) (ordered : i ≤ j)
    (short : interiorVariation
      (((K.folding.projectedBoundaryChain full).inComplexFrame L).polarVariation (L control))
        i j < Real.pi / 4) :
    |K.projectedMetricHeadingError full i - K.projectedMetricHeadingError full j| ≤ η := by
  by_cases equal : i = j
  · simpa only [equal, sub_self, abs_zero] using nonnegative
  have before : i.val < j.val := (lt_of_le_of_ne ordered equal : i < j)
  let n := j.val - i.val - 1
  have fits : i.val + (n + 1) ≤ m := by
    have bound := j.isLt
    dsimp only [n]
    omega
  let P := K.folding.projectedBoundaryChain full
  have index : (⟨i.val + n + 1, by omega⟩ : Fin (m + 1)) = j := by
    apply Fin.ext
    change i.val + n + 1 = j.val
    dsimp only [n]
    omega
  have angles := P.interval_internal_angle_sum_in_frame L control genuine i.val
    (show i.val + (n + 2) ≤ m + 1 by omega)
  have same : interiorVariation ((P.inComplexFrame L).polarVariation (L control))
      ⟨i.val, by omega⟩ ⟨i.val + n + 1, by omega⟩ =
      interiorVariation ((P.inComplexFrame L).polarVariation (L control)) i j :=
    congrArg (fun k : Fin (m + 1) =>
      interiorVariation ((P.inComplexFrame L).polarVariation (L control)) i k) index
  have interval_short : (∑ k : Fin n, InnerProductGeometry.angle
      ((P.interval i.val (n + 2) (by omega)).internalSourceRay control k.castSucc)
      ((P.interval i.val (n + 2) (by omega)).internalSourceRay control k.succ)) <
      Real.pi / 4 := (angles.trans same).trans_lt short
  have geometry := K.folding.projectedBoundaryChain_interval full i.val (n + 1) fits
  let A := K.folding.projectedBoundaryChain (full.interval i.val (n + 1) fits)
  have actual_short :
      (∑ k : Fin n, InnerProductGeometry.angle
        (A.internalSourceRay control k.castSucc) (A.internalSourceRay control k.succ)) <
        Real.pi / 4 := Eq.mpr (congrArg (fun A : PolygonalChain Plane (n + 2) =>
      (∑ k : Fin n, InnerProductGeometry.angle
        (A.internalSourceRay control k.castSucc) (A.internalSourceRay control k.succ)) <
        Real.pi / 4) geometry) interval_short
  have estimate := comparisons.phase_difference i.val n fits actual_short
  have evaluated : |K.projectedMetricHeadingError full j -
      K.projectedMetricHeadingError full i| < η := Eq.mp
    (congrArg (fun k : Fin (m + 1) => |K.projectedMetricHeadingError full k -
      K.projectedMetricHeadingError full i| < η) index) estimate
  exact (abs_sub_comm _ _).trans_le evaluated.le

end Unfoldings.ConvexRoof
