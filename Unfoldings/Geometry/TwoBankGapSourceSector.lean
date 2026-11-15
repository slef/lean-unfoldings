module

public import Unfoldings.Geometry.TwoBankGapLocalSide
public import Unfoldings.Geometry.BankInitialSegment
public import Unfoldings.Metric.Polygonal

/-! Exact source sectors of actual polygonal Jordan gaps with initial straight banks. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

/-- The actual relative angle of the original two initial edge vectors. -/
def initialGapAngle (d e : ℂ) : ℝ := ((e / (‖e‖ : ℂ)) / (d / (‖d‖ : ℂ))).arg

/-- A rigidly oriented geometric sector based at the actual common source. -/
def initialGapSector (source d e : ℂ) : Set ℂ :=
  ((LinearMap.mulLeft ℝ (d / (‖d‖ : ℂ))⁻¹).toAffineMap.comp
    (AffineMap.id ℝ ℂ - AffineMap.const ℝ ℂ source)) ⁻¹' planarSector (initialGapAngle d e)

theorem convex_initialGapSector (source d e : ℂ) : Convex ℝ (initialGapSector source d e) :=
  (convex_planarSector (initialGapAngle d e)).affine_preimage _

theorem source_mem_initialGapSector (source d e : ℂ) : source ∈ initialGapSector source d e := by
  change (d / (‖d‖ : ℂ))⁻¹ * (source - source) ∈ planarSector (initialGapAngle d e)
  rw [sub_self, mul_zero]
  exact ⟨0, le_rfl, 0, le_rfl, by simp⟩

namespace PolygonalRay

variable {n m : ℕ} (R : PolygonalRay ℂ n) (Q : PolygonalRay ℂ m)
  (first_outward : R.Outward) (first_nonzero : R.direction ≠ 0)
  (last_outward : Q.Outward) (last_nonzero : Q.direction ≠ 0)
  (positive_phase : ∀ r : ℝ≥0, 0 < r →
    0 < (R.twoBankRatio Q first_outward first_nonzero last_outward last_nonzero r).im)

/-- The original initial straight pieces give the exact relative opening at every small radius. -/
theorem twoBankAngle_eq_of_initial_segments (d e : ℂ) (first : d ≠ 0) (last : e ≠ 0)
    (first_segment : segment ℝ R.start (R.start + d) ⊆ R.carrier)
    (last_segment : segment ℝ Q.start (Q.start + e) ⊆ Q.carrier)
    (r : ℝ≥0) (positive : 0 < r) (before_first : (r : ℝ) ≤ ‖d‖)
    (before_last : (r : ℝ) ≤ ‖e‖) :
    R.twoBankAngle Q first_outward first_nonzero last_outward last_nonzero r =
      initialGapAngle d e := by
  rw [twoBankAngle, ite_eq_right positive.ne', twoBankRatio,
    R.radialCoefficient_eq_of_initial_segment first_outward first_nonzero d first
      first_segment r positive before_first,
    Q.radialCoefficient_eq_of_initial_segment last_outward last_nonzero e last
      last_segment r positive before_last]
  rfl

/-- The actual geometric gap agrees on a full source neighborhood with its original edge sector. -/
theorem mem_twoBankGap_iff_initialGapSector (d e : ℂ) (first : d ≠ 0) (last : e ≠ 0)
    (first_segment : segment ℝ R.start (R.start + d) ⊆ R.carrier)
    (last_segment : segment ℝ Q.start (Q.start + e) ⊆ Q.carrier)
    (z : ℂ) (near : dist z R.start < min ‖d‖ ‖e‖) :
    z ∈ R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase ↔
      z ∈ initialGapSector R.start d e := by
  let H := R.bankFrame first_outward first_nonzero
  let w := H.symm z
  have radius : ‖w‖ = ‖z - R.start‖ := R.norm_bankFrame_symm first_outward first_nonzero z
  have small : ‖w‖ < min ‖d‖ ‖e‖ := by rwa [radius, ← dist_eq_norm]
  have fixed : z = R.start + (d / (‖d‖ : ℂ)) * w := by
    have same := R.bankFrame_eq_of_initial_segment first_outward first_nonzero d first
      first_segment w (small.le.trans (min_le_left _ _))
    change H (H.symm z) = _ at same
    rwa [H.apply_symm_apply] at same
  have coefficient_nonzero : d / (‖d‖ : ℂ) ≠ 0 :=
    div_ne_zero first (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr first))
  have coordinates : (d / (‖d‖ : ℂ))⁻¹ * (z - R.start) = w := by
    rw [fixed, add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ coefficient_nonzero, one_mul]
  change z ∈ R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase ↔
    (d / (‖d‖ : ℂ))⁻¹ * (z - R.start) ∈ planarSector (initialGapAngle d e)
  rw [coordinates, R.mem_twoBankGap_iff_variable Q first_outward first_nonzero
    last_outward last_nonzero positive_phase, mem_variableSectorGap_iff]
  by_cases zero : w = 0
  · have origin (angle : ℝ) : (0 : ℂ) ∈ planarSector angle :=
      ⟨0, le_rfl, 0, le_rfl, by simp⟩
    change w ∈ planarSector _ ↔ w ∈ planarSector _
    simp only [zero, origin]
  · change w ∈ planarSector
      (R.twoBankAngle Q first_outward first_nonzero last_outward last_nonzero ‖w‖₊) ↔ _
    rw [R.twoBankAngle_eq_of_initial_segments Q first_outward first_nonzero last_outward
      last_nonzero d e first last first_segment last_segment ‖w‖₊ (nnnorm_pos.mpr zero)
      (small.le.trans (min_le_left _ _)) (small.le.trans (min_le_right _ _))]

include positive_phase in
/-- The actual initial opening is a genuine angle strictly between zero and pi. -/
theorem initialGapAngle_bounds (d e : ℂ) (first : d ≠ 0) (last : e ≠ 0)
    (first_segment : segment ℝ R.start (R.start + d) ⊆ R.carrier)
    (last_segment : segment ℝ Q.start (Q.start + e) ⊆ Q.carrier) :
    0 < initialGapAngle d e ∧ initialGapAngle d e < Real.pi := by
  have minimum_positive : 0 < min ‖d‖ ‖e‖ :=
    lt_min (norm_pos_iff.mpr first) (norm_pos_iff.mpr last)
  let r : ℝ≥0 := ⟨min ‖d‖ ‖e‖ / 2, (half_pos minimum_positive).le⟩
  have positive : 0 < r := half_pos minimum_positive
  have before : (r : ℝ) ≤ min ‖d‖ ‖e‖ := by
    change min ‖d‖ ‖e‖ / 2 ≤ min ‖d‖ ‖e‖
    linarith
  have imaginary := positive_phase r positive
  rw [twoBankRatio,
    R.radialCoefficient_eq_of_initial_segment first_outward first_nonzero d first
      first_segment r positive (before.trans (min_le_left _ _)),
    Q.radialCoefficient_eq_of_initial_segment last_outward last_nonzero e last
      last_segment r positive (before.trans (min_le_right _ _))] at imaginary
  constructor
  · apply lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr imaginary.le)
    intro zero
    exact imaginary.ne' (Complex.arg_eq_zero_iff.mp zero.symm).2
  · exact Complex.arg_lt_pi_iff.mpr (Or.inr imaginary.ne')

/-- The actual common sector source belongs to the constructed geometric gap. -/
theorem source_mem_twoBankGap :
    R.start ∈ R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero
      positive_phase := by
  refine ⟨0, ⟨0, le_rfl, 0, le_rfl, by simp⟩, ?_⟩
  simpa only [NNReal.coe_zero, Complex.ofReal_zero, R.radialPoint_zero] using
    R.twoBankFrame_real Q first_outward first_nonzero last_outward last_nonzero positive_phase 0

/-- The source with its actual intrinsic gap metric. -/
def twoBankSourcePoint : PolygonalPoint
    (R.twoBankGap Q first_outward first_nonzero last_outward last_nonzero positive_phase) :=
  ⟨R.start, R.source_mem_twoBankGap Q first_outward first_nonzero last_outward last_nonzero
    positive_phase⟩

end PolygonalRay
end Unfoldings
