module

public import Unfoldings.Geometry.HingeTurnBound
public import Unfoldings.Geometry.ComplexArea
public import Unfoldings.Cone.Sector

/-! Local hinge estimates in a fixed complex frame, including rigid phase alignment. -/

@[expose] public section

namespace Unfoldings

/-- The common strict-halfplane hinge estimate in complex coordinates. -/
theorem complex_hinge_section_angle_le_of_product_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r x y : ℂ} (sides : 0 < (starRingEnd ℂ r * x).im * (starRingEnd ℂ r * y).im)
    (edge a b : E)
    (first_angle : InnerProductGeometry.angle r x = InnerProductGeometry.angle edge a)
    (last_angle : InnerProductGeometry.angle r y = InnerProductGeometry.angle edge b) :
    InnerProductGeometry.angle x y ≤ InnerProductGeometry.angle a b := by
  let L := Complex.orthonormalBasisOneI.repr
  have first : InnerProductGeometry.angle (L r) (L x) =
      InnerProductGeometry.angle edge a := (L.toLinearIsometry.angle_map _ _).trans first_angle
  have last : InnerProductGeometry.angle (L r) (L y) =
      InnerProductGeometry.angle edge b := (L.toLinearIsometry.angle_map _ _).trans last_angle
  have halfplane : 0 < orient 0 (L r) (L x) * orient 0 (L r) (L y) := by
    simpa only [L, orient_complex_repr_zero] using sides
  have bound := hinge_section_angle_le_of_product_pos halfplane edge a b first last
  exact le_trans (L.toLinearIsometry.angle_map x y).symm.le bound

/-- Multiplication by a unit complex number preserves signed area. -/
theorem complex_cross_mul_unit (z x y : ℂ) (unit : ‖z‖ = 1) :
    (starRingEnd ℂ (z * x) * (z * y)).im = (starRingEnd ℂ x * y).im := by
  have norm_squared : z.re ^ 2 + z.im ^ 2 = 1 := by
    have identity := Complex.normSq_eq_norm_sq z
    rw [unit, one_pow] at identity
    simpa only [Complex.normSq_apply, pow_two] using identity
  have expression : (starRingEnd ℂ (z * x) * (z * y)).im =
      (z.re ^ 2 + z.im ^ 2) * (starRingEnd ℂ x * y).im := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [expression, norm_squared, one_mul]

end Unfoldings
