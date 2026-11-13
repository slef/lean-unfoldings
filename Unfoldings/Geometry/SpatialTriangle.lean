module

public import Unfoldings.Geometry.TwoVectorFrame
public import Unfoldings.Cap.Projection
public import Unfoldings.Geometry.Triangle

/-! Genuine spatial triangles have rigid planar coordinates, constructed by Gram--Schmidt. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- Three points with positive Gram determinant have a nondegenerate Euclidean triangle
and a rigid placement carrying its corners to precisely those three spatial points. -/
theorem exists_spatial_triangle (a b c : Space)
    (genuine : (inner ℝ (b - a) (c - a)) ^ 2 < ‖b - a‖ ^ 2 * ‖c - a‖ ^ 2) :
    ∃ (T : Triangle) (place : Plane →ᵃⁱ[ℝ] Space),
      place (T.vertex 0) = a ∧ place (T.vertex 1) = b ∧ place (T.vertex 2) = c := by
  let u := b - a
  let v := c - a
  have nonzero : u ≠ 0 := by
    intro zero
    change (inner ℝ u v) ^ 2 < ‖u‖ ^ 2 * ‖v‖ ^ 2 at genuine
    simp only [zero, inner_zero_left, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul] at genuine
    exact (lt_irrefl _ genuine)
  obtain ⟨B, x, y, nonnegative, first, last⟩ :=
    exists_basis_two_vector_decomposition u v nonzero
  have unit : ‖B 0‖ = 1 := B.orthonormal.1 0
  have positive : 0 < y := by
    by_contra not_positive
    have zero : y = 0 := le_antisymm (le_of_not_gt not_positive) nonnegative
    rw [zero, zero_smul, add_zero] at last
    have scalar : inner ℝ u v = ‖u‖ * x := by
      calc
        _ = inner ℝ (‖u‖ • B 0) (x • B 0) := congrArg₂ (inner ℝ) first last
        _ = _ := by
          rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, unit]
          ring
    have normed : ‖v‖ = |x| := by
      rw [last, norm_smul, unit, mul_one, Real.norm_eq_abs]
    change (inner ℝ u v) ^ 2 < ‖u‖ ^ 2 * ‖v‖ ^ 2 at genuine
    rw [scalar, normed, mul_pow, sq_abs] at genuine
    exact (lt_irrefl _ genuine)
  let L : Plane →ₗᵢ[ℝ] Space :=
    B.repr.symm.toLinearIsometry.comp Cap.horizontalLiftIsometry
  let vec (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]
  have mapped (x y : ℝ) : L (vec x y) = x • B 0 + y • B 1 := by
    change B.repr.symm (Cap.horizontalLift (vec x y)) = _
    rw [← B.repr_symm_single 0, ← B.repr_symm_single 1, ← map_smul, ← map_smul, ← map_add]
    congr 1
    ext i
    fin_cases i <;> simp [Cap.horizontalLift, vec, EuclideanSpace.single]
  let T : Triangle :=
    { vertex := ![0, vec ‖u‖ 0, vec x y]
      nondegenerate := by
        change orient 0 (vec ‖u‖ 0) (vec x y) ≠ 0
        simpa only [orient, vec, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          PiLp.zero_apply, sub_zero, zero_mul, sub_zero] using
          (mul_ne_zero (norm_ne_zero_iff.mpr nonzero) positive.ne') }
  let place : Plane →ᵃⁱ[ℝ] Space :=
    (AffineIsometryEquiv.vaddConst ℝ a).toAffineIsometry.comp L.toAffineIsometry
  refine ⟨T, place, ?_, ?_, ?_⟩
  · change L 0 + a = a
    rw [map_zero, zero_add]
  · change L (vec ‖u‖ 0) + a = b
    rw [mapped, zero_smul, add_zero, ← first]
    exact sub_add_cancel b a
  · change L (vec x y) + a = c
    rw [mapped, ← last]
    exact sub_add_cancel c a

end Unfoldings
