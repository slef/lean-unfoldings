module

public import Unfoldings.FewestNets.LatitudeFrame
public import Mathlib.LinearAlgebra.Determinant

/-! All east-south-outward latitude charts have the same orientation. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

open Real Module

/-- The east-south-outward frame reverses the standard ambient orientation
at every latitude and meridian. -/
theorem latitudeFrame_det (ell longitude : ℝ) :
    LinearMap.det (latitudeFrame ell longitude).toLinearEquiv.toLinearMap = -1 := by
  let std := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let frame := (latitudeFrame ell longitude).toLinearEquiv.toLinearMap
  have axes_det : std.det (latitudeAxes ell longitude) = -1 := by
    rw [Basis.det_apply, Matrix.det_fin_three]
    simp only [std, Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, latitudeAxes, latitudeEast, latitudeSouth, latitudeSite]
    norm_num
    have norm_angle := sin_sq_add_cos_sq ell
    have norm_longitude := sin_sq_add_cos_sq longitude
    linear_combination
      -norm_angle * (sin longitude ^ 2 + cos longitude ^ 2) - norm_longitude
  have on_axes : frame ∘ latitudeAxes ell longitude = (std : Fin 3 → Space) := by
    funext j
    ext i
    change latitudeFrame ell longitude (latitudeAxes ell longitude j) i = std j i
    rw [latitudeFrame_coordinate, (orthonormal_iff_ite.mp (latitudeAxes_orthonormal ell longitude)) i j]
    simp only [std, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single, PiLp.single_apply]
  have formula := std.det_comp frame (latitudeAxes ell longitude)
  rw [on_axes, std.det_self, axes_det, mul_neg_one] at formula
  linarith only [formula]

end Unfoldings.FewestNets
