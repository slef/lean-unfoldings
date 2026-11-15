module

public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! Radius-dependent invertible linear changes of direction give ambient homeomorphisms. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalize each linear image back onto its original sphere. The radius-zero map is immaterial. -/
def radialLinearMap (L : ℝ≥0 → E ≃L[ℝ] E) (z : E) : E :=
  ‖z‖ • NormedSpace.normalize (L ‖z‖₊ z)

@[simp] theorem radialLinearMap_zero (L : ℝ≥0 → E ≃L[ℝ] E) : radialLinearMap L 0 = 0 := by
  simp [radialLinearMap]

@[simp] theorem norm_radialLinearMap (L : ℝ≥0 → E ≃L[ℝ] E) (z : E) :
    ‖radialLinearMap L z‖ = ‖z‖ := by
  by_cases zero : z = 0
  · simp [zero]
  · have nonzero : L ‖z‖₊ z ≠ 0 := by
      simpa only [map_zero] using (L ‖z‖₊).injective.ne zero
    rw [radialLinearMap, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z),
      NormedSpace.norm_normalize nonzero, mul_one]

@[simp] theorem nnnorm_radialLinearMap (L : ℝ≥0 → E ≃L[ℝ] E) (z : E) :
    ‖radialLinearMap L z‖₊ = ‖z‖₊ := NNReal.eq (norm_radialLinearMap L z)

theorem radialLinearMap_left_inverse (L : ℝ≥0 → E ≃L[ℝ] E) (z : E) :
    radialLinearMap (fun r => (L r).symm) (radialLinearMap L z) = z := by
  by_cases zero : z = 0
  · simp [zero]
  · have nonzero : L ‖z‖₊ z ≠ 0 := by
      simpa only [map_zero] using (L ‖z‖₊).injective.ne zero
    have inverse_value : (L ‖z‖₊).symm (radialLinearMap L z) =
        (‖z‖ * ‖L ‖z‖₊ z‖⁻¹) • z := by
      rw [radialLinearMap, NormedSpace.normalize, map_smul, map_smul,
        ContinuousLinearEquiv.symm_apply_apply, smul_smul]
    change ‖radialLinearMap L z‖ • NormedSpace.normalize
      ((L ‖radialLinearMap L z‖₊).symm (radialLinearMap L z)) = z
    rw [norm_radialLinearMap, nnnorm_radialLinearMap, inverse_value,
      NormedSpace.normalize_smul_of_pos
        (mul_pos (norm_pos_iff.mpr zero) (inv_pos.mpr (norm_pos_iff.mpr nonzero))),
      NormedSpace.norm_smul_normalize]

/-- A direction change that already has the right radius needs no normalization. -/
theorem radialLinearMap_eq_linear_of_norm (L : ℝ≥0 → E ≃L[ℝ] E) (z : E)
    (same : ‖L ‖z‖₊ z‖ = ‖z‖) : radialLinearMap L z = L ‖z‖₊ z := by
  by_cases zero : z = 0
  · simp [zero]
  · rw [radialLinearMap, NormedSpace.normalize, same, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr zero), one_smul]

theorem continuousAt_normalize_of_ne_zero {z : E} (nonzero : z ≠ 0) :
    ContinuousAt (NormedSpace.normalize : E → E) z := by
  unfold NormedSpace.normalize
  exact (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr nonzero)).smul
    continuous_id.continuousAt

variable (L : ℝ≥0 → E ≃L[ℝ] E)
  (regular : ContinuousOn (fun p : ℝ≥0 × E => L p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))

include regular in
/-- No limit of the directional linear maps at radius zero is required. -/
theorem continuous_radialLinearMap : Continuous (radialLinearMap L) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases zero : z = 0
  · subst z
    apply Metric.continuousAt_iff.mpr
    intro ε positive
    refine ⟨ε, positive, ?_⟩
    intro w close
    simpa only [radialLinearMap_zero, dist_zero_right, norm_radialLinearMap] using close
  · have inside : (‖z‖₊, z) ∈ Set.Ioi (0 : ℝ≥0) ×ˢ Set.univ :=
      ⟨nnnorm_pos.mpr zero, Set.mem_univ z⟩
    have evaluation : ContinuousAt (fun p : ℝ≥0 × E => L p.1 p.2) (‖z‖₊, z) :=
      regular.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds inside)
    have raw : ContinuousAt (fun w : E => L ‖w‖₊ w) z :=
      evaluation.comp (f := fun w : E => (‖w‖₊, w))
        (continuous_nnnorm.prodMk continuous_id).continuousAt
    have nonzero : L ‖z‖₊ z ≠ 0 := by
      simpa only [map_zero] using (L ‖z‖₊).injective.ne zero
    exact continuous_norm.continuousAt.smul
      ((continuousAt_normalize_of_ne_zero nonzero).comp (f := fun w : E => L ‖w‖₊ w) raw)

/-- Continuous radius-dependent linear direction changes extend to a homeomorphism of the
whole space, preserving every sphere, including when the changes degenerate near the center. -/
def radialLinearHomeomorph
    (inverse_regular : ContinuousOn (fun p : ℝ≥0 × E => (L p.1).symm p.2)
      (Set.Ioi 0 ×ˢ Set.univ)) : E ≃ₜ E where
  toFun := radialLinearMap L
  invFun := radialLinearMap (fun r => (L r).symm)
  left_inv := radialLinearMap_left_inverse L
  right_inv z := by
    simpa only [ContinuousLinearEquiv.symm_symm] using
      radialLinearMap_left_inverse (fun r => (L r).symm) z
  continuous_toFun := continuous_radialLinearMap L regular
  continuous_invFun := continuous_radialLinearMap _ inverse_regular

@[simp] theorem radialLinearHomeomorph_apply
    (inverse_regular : ContinuousOn (fun p : ℝ≥0 × E => (L p.1).symm p.2)
      (Set.Ioi 0 ×ˢ Set.univ)) (z : E) :
    radialLinearHomeomorph L regular inverse_regular z =
      ‖z‖ • NormedSpace.normalize (L ‖z‖₊ z) := rfl

end Unfoldings
