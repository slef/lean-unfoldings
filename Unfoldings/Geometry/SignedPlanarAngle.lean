module

public import Unfoldings.Geometry.Triangle
public import Mathlib.Analysis.Complex.Angle

/-! A consistent signed real lift of the angle between two planar rays. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open Real InnerProductGeometry

/-- The standard oriented complex chart, with the second axis pointing north. -/
abbrev orientedComplex : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

@[simp] theorem orientedComplex_re (p : Plane) : (orientedComplex p).re = p 0 := by
  simp [orientedComplex, Complex.orthonormalBasisOneI_repr_symm_apply]

@[simp] theorem orientedComplex_im (p : Plane) : (orientedComplex p).im = p 1 := by
  simp [orientedComplex, Complex.orthonormalBasisOneI_repr_symm_apply]

/-- Signed angle from the first ray to the second, in the interval (-π, π]. -/
def signedPlanarAngle (p q : Plane) : ℝ := (orientedComplex q / orientedComplex p).arg

theorem signedPlanarAngle_coe (p q : Plane) (hp : p ≠ 0) (hq : q ≠ 0) :
    (signedPlanarAngle p q : Real.Angle) =
      ((orientedComplex q).arg : Real.Angle) - (orientedComplex p).arg :=
  Complex.arg_div_coe_angle (orientedComplex.map_ne_zero_iff.mpr hq)
    (orientedComplex.map_ne_zero_iff.mpr hp)

theorem abs_signedPlanarAngle (p q : Plane) (hp : p ≠ 0) (hq : q ≠ 0) :
    |signedPlanarAngle p q| = angle p q := by
  have hf := Complex.angle_eq_abs_arg (orientedComplex.map_ne_zero_iff.mpr hq)
    (orientedComplex.map_ne_zero_iff.mpr hp)
  exact hf.symm.trans ((orientedComplex.toLinearIsometry.angle_map q p).trans (angle_comm _ _))

theorem signedPlanarAngle_nonneg_iff (p q : Plane) (hp : p ≠ 0) :
    0 ≤ signedPlanarAngle p q ↔ 0 ≤ p 0 * q 1 - p 1 * q 0 := by
  have np := Complex.normSq_pos.mpr (orientedComplex.map_ne_zero_iff.mpr hp)
  rw [signedPlanarAngle, Complex.arg_nonneg_iff, Complex.div_im, orientedComplex_re,
    orientedComplex_re, orientedComplex_im, orientedComplex_im, ← sub_div]
  rw [div_nonneg_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · linarith only [h]
    · exact (not_le_of_gt np h).elim
  · intro h
    exact Or.inl ⟨by linarith only [h], np.le⟩

@[simp] theorem signedPlanarAngle_neg_neg (p q : Plane) :
    signedPlanarAngle (-p) (-q) = signedPlanarAngle p q := by
  simp only [signedPlanarAngle, map_neg, neg_div_neg_eq]

theorem signedPlanarAngle_smul_of_pos {t s : ℝ} (tp : 0 < t) (sp : 0 < s) (p q : Plane) :
    signedPlanarAngle (t • p) (s • q) = signedPlanarAngle p q := by
  unfold signedPlanarAngle
  rw [map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have h : ((s : ℂ) * orientedComplex q) / ((t : ℂ) * orientedComplex p) =
      ((s / t : ℝ) : ℂ) * (orientedComplex q / orientedComplex p) := by
    simp only [div_eq_mul_inv, mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv]
    ring
  rw [h, Complex.arg_real_mul _ (div_pos sp tp)]

end Unfoldings
