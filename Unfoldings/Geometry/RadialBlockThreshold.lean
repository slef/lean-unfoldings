module

public import Unfoldings.Geometry.RadialBlockError
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Mesh-independent small speed and local heading budgets make weighted radial loss small. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem radialBlockError_mono_speed {S T B C K δ : ℝ} (ordered : S ≤ T)
    (budget : 0 ≤ B) (constant : 0 ≤ C) (angular : 0 ≤ K) (width : 0 < δ) :
    radialBlockError S B C K δ ≤ radialBlockError T B C K δ := by
  unfold radialBlockError
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (sub_le_sub_right ordered 1) constant
  · have coefficient : 0 ≤ B * C * (1 + C * K / δ) := by positivity
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right ordered coefficient

/-- The numerical choice precedes the entire bank and mesh. Every smaller positive tilt
has the same small weighted radial loss at this fixed positive local heading tolerance. -/
theorem exists_positive_radialBlock_threshold {ε C K δ : ℝ} (positive : 0 < ε)
    (constant : 0 ≤ C) (angular : 0 ≤ K) (width : 0 < δ) :
    ∃ B > 0, ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∀ ψ ∈ Set.Ioc (0 : ℝ) φ, (3 : ℝ) / 4 ≤ Real.cos ψ ∧
        radialBlockError (Real.cos ψ)⁻¹ B C K δ < ε := by
  let F := 1 + C * K / δ
  have Fpositive : 0 < F := by dsimp [F]; positivity
  have Cpositive : 0 < C + 1 := by positivity
  let B := ε / (4 * (C + 1) * F)
  have Bpositive : 0 < B := by dsimp [B]; positivity
  let loss (φ : ℝ) := radialBlockError (Real.cos φ)⁻¹ B C K δ
  have at_zero : loss 0 = (ε / 4) * (C / (C + 1)) := by
    dsimp [loss, radialBlockError, B, F]
    simp only [Real.cos_zero, inv_one, sub_self, mul_zero, one_mul, zero_add]
    field_simp [Cpositive.ne', Fpositive.ne']
  have zero_small : loss 0 < ε := by
    rw [at_zero]
    have ratio : C / (C + 1) < 1 := (div_lt_one Cpositive).mpr (by linarith)
    have bound := mul_lt_mul_of_pos_left ratio (show 0 < ε / 4 by positivity)
    rw [mul_one] at bound
    exact bound.trans (by linarith)
  have continuous : ContinuousAt loss 0 := by
    dsimp [loss, radialBlockError]
    fun_prop (disch := norm_num)
  have near_loss : ∀ᶠ φ in nhds (0 : ℝ), loss φ < ε :=
    continuous.eventually (gt_mem_nhds zero_small)
  have near_cos : ∀ᶠ φ in nhds (0 : ℝ), (3 : ℝ) / 4 < Real.cos φ :=
    Real.continuous_cos.continuousAt.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨r, rpositive, near⟩ := Metric.eventually_nhds_iff.mp (near_loss.and near_cos)
  let φ := min (r / 2) (Real.pi / 4)
  have φpositive : 0 < φ := lt_min (by positivity) (by positivity)
  have φsmall : φ < Real.pi / 2 := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  have φclose : dist φ 0 < r := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos φpositive]
    exact (min_le_left _ _).trans_lt (by linarith)
  have good := near φclose
  refine ⟨B, Bpositive, φ, ⟨φpositive, φsmall⟩, ?_⟩
  intro ψ bounds
  have cos_order : Real.cos φ ≤ Real.cos ψ :=
    Real.cos_le_cos_of_nonneg_of_le_pi bounds.1.le (by linarith [Real.pi_pos]) bounds.2
  have φ_cos_positive : 0 < Real.cos φ := by linarith [good.2]
  have ψ_cos_positive : 0 < Real.cos ψ := φ_cos_positive.trans_le cos_order
  refine ⟨good.2.le.trans cos_order, ?_⟩
  have speed : (Real.cos ψ)⁻¹ ≤ (Real.cos φ)⁻¹ :=
    (inv_le_inv₀ ψ_cos_positive φ_cos_positive).mpr cos_order
  exact (radialBlockError_mono_speed speed Bpositive.le constant angular width).trans_lt good.1

end Unfoldings
