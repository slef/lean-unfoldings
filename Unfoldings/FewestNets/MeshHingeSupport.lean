module

public import Unfoldings.FewestNets.MeshBisectors
public import Unfoldings.Geometry.AcuteSphericalHinge
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! An actual mesh triangle's cross-product normal strictly supports its adjacent triangle. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets

/-- The normalized affine support of a radial triangle is determined by the
three values on its linearly independent vertices. -/
theorem scaled_support_eq_of_radial_triangle {a b c n m : Space}
    (independent : LinearIndependent ℝ ![a, b, c])
    (n_ne : inner ℝ n a ≠ 0) (m_ne : inner ℝ m a ≠ 0)
    (nb : inner ℝ n b = inner ℝ n a) (nc : inner ℝ n c = inner ℝ n a)
    (mb : inner ℝ m b = inner ℝ m a) (mc : inner ℝ m c = inner ℝ m a) (z : Space) :
    inner ℝ n z / inner ℝ n a = inner ℝ m z / inner ℝ m a := by
  let L := (inner ℝ n a)⁻¹ • (innerSL ℝ n).toLinearMap
  let M := (inner ℝ m a)⁻¹ • (innerSL ℝ m).toLinearMap
  have span := independent.span_eq_top_of_card_eq_finrank (by simp [Space])
  have same : L = M := LinearMap.ext_on_range span (by
    intro i
    fin_cases i <;>
      simp [L, M, nb, nc, mb, mc, n_ne, m_ne, smul_eq_mul])
  have h := congrArg (fun f : Space →ₗ[ℝ] ℝ => f z) same
  change (inner ℝ n a)⁻¹ * inner ℝ n z = (inner ℝ m a)⁻¹ * inner ℝ m z at h
  simpa only [div_eq_inv_mul] using h

/-- A pair of radially adjacent acute chord triangles gives the strict hinge
inequality for the same cross-product normal used in the geometric checker. -/
theorem spatialCross_strict_support_of_acute_hinge {a b c d : Space}
    (au : ‖a‖ = 1) (bu : ‖b‖ = 1) (cu : ‖c‖ = 1) (du : ‖d‖ = 1)
    (not_antipodal : a + b ≠ 0)
    (independent : LinearIndependent ℝ ![a, b, c])
    (side_c : 0 < inner ℝ (spatialCross a b) c)
    (side_d : inner ℝ (spatialCross a b) d < 0)
    (acute_c : InnerProductGeometry.angle (a - c) (b - c) < Real.pi / 2)
    (acute_d : InnerProductGeometry.angle (a - d) (b - d) < Real.pi / 2)
    (outward : 0 < inner ℝ (spatialCross (b - a) (c - a)) a) :
    inner ℝ (spatialCross (b - a) (c - a)) d <
      inner ℝ (spatialCross (b - a) (c - a)) a := by
  let m := spatialCross (b - a) (c - a)
  have oa : inner ℝ (spatialCross a b) a = 0 :=
    (real_inner_comm a _).trans (inner_left_spatialCross a b)
  have ob : inner ℝ (spatialCross a b) b = 0 :=
    (real_inner_comm b _).trans (inner_right_spatialCross a b)
  obtain ⟨n, npos, nb, nc, nd⟩ := exists_strict_support_of_acute_spherical_hinge
    au bu cu du not_antipodal oa ob side_c side_d acute_c acute_d
  have mb : inner ℝ m b = inner ℝ m a := by
    have h : inner ℝ (b - a) m = 0 := inner_left_spatialCross _ _
    rw [real_inner_comm m (b - a), inner_sub_right, sub_eq_zero] at h
    exact h
  have mc : inner ℝ m c = inner ℝ m a := by
    have h : inner ℝ (c - a) m = 0 := inner_right_spatialCross _ _
    rw [real_inner_comm m (c - a), inner_sub_right, sub_eq_zero] at h
    exact h
  have eq := scaled_support_eq_of_radial_triangle independent npos.ne' outward.ne'
    nb.symm nc.symm mb mc d
  have frac : inner ℝ n d / inner ℝ n a < 1 := (div_lt_one npos).mpr nd
  exact (div_lt_one outward).mp (eq ▸ frac)

end Unfoldings.FewestNets
