module

public import Unfoldings.Geometry.TwoBankGapSourceChart
public import Unfoldings.Metric.BallIsometry
public import Mathlib.Analysis.Complex.Isometry

/-! Rigid coordinates for the actual geometric source sector and its canonical metric sector. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

/-- The source-sector coordinate change is a genuine rigid isometry, with the actual edge axis. -/
def initialGapSectorIsometryEquiv (source d e : ℂ) (genuine : d ≠ 0) :
    planarSector (initialGapAngle d e) ≃ᵢ initialGapSector source d e := by
  let c := d / (‖d‖ : ℂ)
  have nonzero : c ≠ 0 := div_ne_zero genuine
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr genuine))
  have unit : ‖c‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg d)]
    exact div_self (norm_ne_zero_iff.mpr genuine)
  refine
    { toFun := fun x => ⟨source + c * x.val, ?_⟩
      invFun := fun y => ⟨c⁻¹ * (y.val - source), y.property⟩
      left_inv := ?_
      right_inv := ?_
      isometry_toFun := ?_ }
  · change c⁻¹ * (source + c * x.val - source) ∈ planarSector (initialGapAngle d e)
    rw [add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ nonzero, one_mul]
    exact x.property
  · intro x
    apply Subtype.ext
    change c⁻¹ * (source + c * x.val - source) = x.val
    rw [add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ nonzero, one_mul]
  · intro y
    apply Subtype.ext
    change source + c * (c⁻¹ * (y.val - source)) = y.val
    rw [← mul_assoc, mul_inv_cancel₀ nonzero, one_mul, add_sub_cancel]
  · apply Isometry.of_dist_eq
    intro x y
    change dist (source + c * x.val) (source + c * y.val) = dist x.val y.val
    rw [dist_add_left, dist_eq_norm, ← mul_sub, norm_mul, unit, one_mul, dist_eq_norm]

@[simp] theorem initialGapSectorIsometryEquiv_apply (source d e : ℂ) (genuine : d ≠ 0)
    (x : planarSector (initialGapAngle d e)) :
    (initialGapSectorIsometryEquiv source d e genuine x).val =
      source + (d / (‖d‖ : ℂ)) * x.val := rfl

@[simp] theorem initialGapSectorIsometryEquiv_symm_apply (source d e : ℂ) (genuine : d ≠ 0)
    (y : initialGapSector source d e) :
    ((initialGapSectorIsometryEquiv source d e genuine).symm y).val =
      (d / (‖d‖ : ℂ))⁻¹ * (y.val - source) := rfl

/-- The genuine canonical sector origin, without an extra angle restriction. -/
def initialGapSectorOrigin (d e : ℂ) : planarSector (initialGapAngle d e) :=
  ⟨0, 0, le_rfl, 0, le_rfl, by simp⟩

/-- Restrict the rigid sector coordinates to the exact physical source ball. -/
def initialGapSectorBallIsometry (source d e : ℂ) (genuine : d ≠ 0) (r : ℝ) :
    Metric.ball (initialGapSectorOrigin d e) r ≃ᵢ
      Metric.ball
        (⟨source, source_mem_initialGapSector source d e⟩ : initialGapSector source d e) r where
  toFun x := ⟨initialGapSectorIsometryEquiv source d e genuine x.val, by
    have center : initialGapSectorIsometryEquiv source d e genuine
        (initialGapSectorOrigin d e) =
        ⟨source, source_mem_initialGapSector source d e⟩ := by
      apply Subtype.ext
      simp only [initialGapSectorIsometryEquiv_apply, initialGapSectorOrigin, mul_zero, add_zero]
    change dist (initialGapSectorIsometryEquiv source d e genuine x.val) _ < r
    rw [← center, (initialGapSectorIsometryEquiv source d e genuine).isometry.dist_eq]
    exact x.property⟩
  invFun y := ⟨(initialGapSectorIsometryEquiv source d e genuine).symm y.val, by
    have center : (initialGapSectorIsometryEquiv source d e genuine).symm
        ⟨source, source_mem_initialGapSector source d e⟩ = initialGapSectorOrigin d e := by
      apply Subtype.ext
      simp only [initialGapSectorIsometryEquiv_symm_apply, initialGapSectorOrigin,
        sub_self, mul_zero]
    change dist ((initialGapSectorIsometryEquiv source d e genuine).symm y.val) _ < r
    rw [← center, (initialGapSectorIsometryEquiv source d e genuine).symm.isometry.dist_eq]
    exact y.property⟩
  left_inv x := Subtype.ext ((initialGapSectorIsometryEquiv source d e genuine).symm_apply_apply _)
  right_inv y := Subtype.ext ((initialGapSectorIsometryEquiv source d e genuine).apply_symm_apply _)
  isometry_toFun x y := (initialGapSectorIsometryEquiv source d e genuine).isometry _ _

/-- The geometric gap angle has exactly the normalized ratio of its original bank vectors. -/
theorem polarRay_initialGapAngle (d e : ℂ) (first : d ≠ 0) (last : e ≠ 0) :
    polarRay (initialGapAngle d e) = (e / (‖e‖ : ℂ)) / (d / (‖d‖ : ℂ)) := by
  have unit (z : ℂ) (nonzero : z ≠ 0) : ‖z / (‖z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
    exact div_self (norm_ne_zero_iff.mpr nonzero)
  have ratio_unit : ‖(e / (‖e‖ : ℂ)) / (d / (‖d‖ : ℂ))‖ = 1 := by
    rw [norm_div, unit e last, unit d first, div_self one_ne_zero]
  have same := Complex.norm_mul_exp_arg_mul_I ((e / (‖e‖ : ℂ)) / (d / (‖d‖ : ℂ)))
  rw [ratio_unit, Complex.ofReal_one, one_mul] at same
  exact same

namespace PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- An actual Jordan gap's intrinsic source ball has canonical sector coordinates given
by the actual first bank vector, with precisely the geometric bank-gap angle. -/
theorem exists_twoBankGap_canonical_source_isometry (d e : ℂ) (first : d ≠ 0) (last : e ≠ 0)
    (first_segment : segment ℝ R.start (R.start + d) ⊆ R.carrier)
    (last_segment : segment ℝ Q.start (Q.start + e) ⊆ Q.carrier) :
    ∃ A : Metric.eball
      (R.twoBankSourcePoint Q first_outward first_nonzero last_outward last_nonzero positive_phase)
        (ENNReal.ofReal (min ‖d‖ ‖e‖)) ≃ᵢ
      Metric.ball (initialGapSectorOrigin d e) (min ‖d‖ ‖e‖),
      ∀ y, (A y).val.val = (d / (‖d‖ : ℂ))⁻¹ * (y.val.val - R.start) := by
  obtain ⟨A, physical⟩ := R.exists_twoBankGap_source_sector_isometry Q first_outward first_nonzero
    last_outward last_nonzero positive_phase d e first last first_segment last_segment
  refine ⟨A.trans (initialGapSectorBallIsometry R.start d e first (min ‖d‖ ‖e‖)).symm, ?_⟩
  intro y
  change (d / (‖d‖ : ℂ))⁻¹ * ((A y).val.val - R.start) = _
  rw [physical]

end PolygonalRay
end Unfoldings
