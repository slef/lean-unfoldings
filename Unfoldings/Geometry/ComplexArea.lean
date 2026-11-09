module

public import Unfoldings.Geometry.Triangle
public import Mathlib.Analysis.Complex.Isometry

/-! Signed planar area in Mathlib's standard complex orthonormal coordinates. -/

@[expose] public section

namespace Unfoldings

theorem orient_complex_repr (a b c : ℂ) :
    orient (Complex.orthonormalBasisOneI.repr a) (Complex.orthonormalBasisOneI.repr b)
      (Complex.orthonormalBasisOneI.repr c) = (starRingEnd ℂ (b - a) * (c - a)).im := by
  simp only [orient, Complex.orthonormalBasisOneI_repr_apply, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem orient_complex_repr_zero (a b : ℂ) :
    orient 0 (Complex.orthonormalBasisOneI.repr a) (Complex.orthonormalBasisOneI.repr b) =
      (starRingEnd ℂ a * b).im := by
  have mapped := orient_complex_repr 0 a b
  simpa only [map_zero, sub_zero] using mapped

end Unfoldings
