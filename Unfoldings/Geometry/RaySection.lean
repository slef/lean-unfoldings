module

public import Unfoldings.Geometry.RadialSlice
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Transverse sections of two-ray wedges

A positive functional level cuts the positive span of two rays in exactly
the segment between their normalized endpoints. The original apex angle is
unchanged by this positive radial normalization. These are the local edges
and lateral angles of a vertex figure.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_segment_radial_normalize_iff (f : E →L[ℝ] ℝ) (u v z : E) (h : ℝ)
    (level_positive : 0 < h) (left_positive : 0 < f u) (right_positive : 0 < f v) :
    z ∈ segment ℝ ((h / f u) • u) ((h / f v) • v) ↔
      f z = h ∧ ∃ a : ℝ, 0 ≤ a ∧ ∃ b : ℝ, 0 ≤ b ∧ z = a • u + b • v := by
  constructor
  · rintro ⟨a, b, ha, hb, sum, equal⟩
    have left_scale : 0 ≤ h / f u := (div_pos level_positive left_positive).le
    have right_scale : 0 ≤ h / f v := (div_pos level_positive right_positive).le
    constructor
    · rw [← equal, map_add, map_smul, map_smul, map_smul, map_smul]
      change a * ((h / f u) * f u) + b * ((h / f v) * f v) = h
      rw [div_mul_cancel₀ _ left_positive.ne', div_mul_cancel₀ _ right_positive.ne']
      rw [← add_mul, sum, one_mul]
    · refine ⟨a * (h / f u), mul_nonneg ha left_scale,
        b * (h / f v), mul_nonneg hb right_scale, ?_⟩
      rw [← equal, smul_smul, smul_smul]
  · rintro ⟨height, a, ha, b, hb, equal⟩
    have weighted : a * f u + b * f v = h := by
      rw [equal, map_add, map_smul, map_smul] at height
      exact height
    have left_nonneg : 0 ≤ a * f u / h := div_nonneg (mul_nonneg ha left_positive.le)
      level_positive.le
    have right_nonneg : 0 ≤ b * f v / h := div_nonneg (mul_nonneg hb right_positive.le)
      level_positive.le
    refine ⟨a * f u / h, b * f v / h, left_nonneg, right_nonneg, ?_, ?_⟩
    · rw [← add_div, weighted, div_self level_positive.ne']
    · have left_cancel : (a * f u / h) * (h / f u) = a := by
        field_simp
      have right_cancel : (b * f v / h) * (h / f v) = b := by
        field_simp
      rw [smul_smul, smul_smul, left_cancel, right_cancel]
      exact equal.symm

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem angle_radial_normalize (f : E →L[ℝ] ℝ) (u v : E) (h : ℝ)
    (level_positive : 0 < h) (left_positive : 0 < f u) (right_positive : 0 < f v) :
    InnerProductGeometry.angle ((h / f u) • u) ((h / f v) • v) =
      InnerProductGeometry.angle u v := by
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (div_pos level_positive left_positive),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (div_pos level_positive right_positive)]

end InnerProduct

end Unfoldings
