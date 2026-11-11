module

public import Unfoldings.Geometry.AcuteWedgeFrame
public import Unfoldings.Geometry.ComplexRotationFrame

/-! A positively oriented acute-wedge frame preserves the sign of actual bank rotations. -/

@[expose] public section

namespace Unfoldings.AcuteWedgeFrame

variable {u v : Plane} (B : AcuteWedgeFrame u v)

/-- The ordered quadrant banks have nonnegative signed area, including a limiting coincident ray. -/
theorem banks_cross_nonneg : 0 ≤ (starRingEnd ℂ (B.place u) * B.place v).im := by
  have cross (r s a b : ℝ) :
      (starRingEnd ℂ ((r : ℂ) * polarRay a) * ((s : ℂ) * polarRay b)).im =
        r * s * Real.sin (b - a) := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, polarRay_re, polarRay_im, Real.sin_sub]
    ring
  rw [B.first, B.last, cross]
  apply mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · linarith [B.small]
  · linarith [B.positive, Real.pi_pos]

/-- Positive original orientation makes the orthogonal wedge frame a complex rotation. -/
theorem complex_frame_commutes_mul (positive : 0 < orient 0 u v) (z w : ℂ) :
    (Complex.orthonormalBasisOneI.repr.trans B.place) (z * w) =
      z * (Complex.orthonormalBasisOneI.repr.trans B.place) w := by
  let F := Complex.orthonormalBasisOneI.repr.trans B.place
  let P := Complex.orthonormalBasisOneI.repr.symm
  have original : 0 < (starRingEnd ℂ (P u) * P v).im := by
    have area := orient_complex_repr_zero (P u) (P v)
    change orient 0 (P.symm (P u)) (P.symm (P v)) = _ at area
    simpa only [P.symm_apply_apply, ← area] using positive
  have map_vector (x : Plane) : F (P x) = B.place x := by
    change B.place (Complex.orthonormalBasisOneI.repr
      (Complex.orthonormalBasisOneI.repr.symm x)) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
  have mapped : 0 ≤ (starRingEnd ℂ (F (P u)) * F (P v)).im := by
    rw [map_vector, map_vector]
    exact B.banks_cross_nonneg
  exact complex_isometry_commutes_mul_of_cross F (P u) (P v) original mapped z w

end Unfoldings.AcuteWedgeFrame
