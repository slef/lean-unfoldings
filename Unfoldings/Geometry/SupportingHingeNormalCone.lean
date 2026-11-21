module

public import Unfoldings.Geometry.RadialTriangleGauge
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! A tie at the shared edge of two supported chord triangles is a nonnegative
combination of their two outward normals. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem exists_nonnegative_combination_of_hinge_tie {a b c d n m x : Space}
    (independent : LinearIndependent ℝ ![a, b, c])
    (na : inner ℝ n a = 1) (nb : inner ℝ n b = 1) (nc : inner ℝ n c = 1) (nd : inner ℝ n d < 1)
    (ma : inner ℝ m a = 1) (mb : inner ℝ m b = 1) (md : inner ℝ m d = 1) (mc : inner ℝ m c < 1)
    (xb : inner ℝ x b = inner ℝ x a) (xc : inner ℝ x c ≤ inner ℝ x a)
    (xd : inner ℝ x d ≤ inner ℝ x a) :
    ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ x = s • n + t • m := by
  let s := inner ℝ x (d - a) / inner ℝ n (d - a)
  let t := inner ℝ x (c - a) / inner ℝ m (c - a)
  have nneg : inner ℝ n (d - a) < 0 := by rwa [inner_sub_right, na, sub_neg]
  have mneg : inner ℝ m (c - a) < 0 := by rwa [inner_sub_right, ma, sub_neg]
  have s_nonnegative : 0 ≤ s := div_nonneg_of_nonpos
    (by rwa [inner_sub_right, sub_nonpos]) nneg.le
  have t_nonnegative : 0 ≤ t := div_nonneg_of_nonpos
    (by rwa [inner_sub_right, sub_nonpos]) mneg.le
  have s_eq : s * inner ℝ n (d - a) = inner ℝ x (d - a) :=
    div_mul_cancel₀ _ nneg.ne
  have t_eq : t * inner ℝ m (c - a) = inner ℝ x (c - a) :=
    div_mul_cancel₀ _ mneg.ne
  let r := x - s • n - t • m
  have b_zero : inner ℝ r (b - a) = 0 := by
    dsimp only [r]
    simp only [inner_sub_left, real_inner_smul_left, inner_sub_right, xb, nb, na, mb, ma,
      sub_self]
  have c_zero : inner ℝ r (c - a) = 0 := by
    have zero : inner ℝ n (c - a) = 0 := by rw [inner_sub_right, nc, na, sub_self]
    dsimp only [r]
    rw [inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left, zero,
      mul_zero, sub_zero, t_eq, sub_self]
  have d_zero : inner ℝ r (d - a) = 0 := by
    have zero : inner ℝ m (d - a) = 0 := by rw [inner_sub_right, md, ma, sub_self]
    dsimp only [r]
    rw [inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left, zero,
      mul_zero, sub_zero, s_eq, sub_self]
  rw [inner_sub_right, sub_eq_zero] at b_zero c_zero
  have proportional : (innerSL ℝ r).toLinearMap =
      (inner ℝ r a) • (innerSL ℝ n).toLinearMap := by
    apply LinearMap.ext_on_range (independent.span_eq_top_of_card_eq_finrank (by simp [Space]))
    intro k
    change inner ℝ r (![a, b, c] k) = inner ℝ r a * inner ℝ n (![a, b, c] k)
    fin_cases k
    · change inner ℝ r a = inner ℝ r a * inner ℝ n a
      rw [na, mul_one]
    · change inner ℝ r b = inner ℝ r a * inner ℝ n b
      rw [b_zero, nb, mul_one]
    · change inner ℝ r c = inner ℝ r a * inner ℝ n c
      rw [c_zero, nc, mul_one]
  have scaled : inner ℝ r a * inner ℝ n (d - a) = 0 :=
    (DFunLike.congr_fun proportional (d - a)).symm.trans d_zero
  have r_a : inner ℝ r a = 0 := (mul_eq_zero.mp scaled).resolve_right nneg.ne
  have r_eq : r = 0 := by
    have h := DFunLike.congr_fun proportional r
    change inner ℝ r r = inner ℝ r a * inner ℝ n r at h
    rw [r_a, zero_mul, real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at h
    exact h
  change x - s • n - t • m = 0 at r_eq
  rw [sub_sub] at r_eq
  exact ⟨s, t, s_nonnegative, t_nonnegative, sub_eq_zero.mp r_eq⟩

end Unfoldings
