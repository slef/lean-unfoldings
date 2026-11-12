module

public import Unfoldings.Cap.SectorBankRays

/-! Actual enclosing-ray banks follow every segment between two positive heights. -/

@[expose] public section

namespace Unfoldings.AcuteWedgeFrame

variable {u v : Plane} (B : AcuteWedgeFrame u v)

theorem enclosingStrip_lower_physical_mem_segment (q : Plane) {a h b : ℝ}
    (nonnegative : 0 ≤ a) (member : h ∈ Set.Icc a b) :
    q + B.place.symm (B.enclosingStrip.lower.point h) ∈ segment ℝ
      (q + B.place.symm (B.enclosingStrip.lower.point a))
      (q + B.place.symm (B.enclosingStrip.lower.point b)) := by
  let direction := ((B.place v).re + (B.place v).im)⁻¹ • v
  let A : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap q (q + direction)
  have value (k : ℝ) (positive : 0 ≤ k) :
      A k = q + B.place.symm (B.enclosingStrip.lower.point k) := by
    rw [B.enclosingStrip_lower_point_ray positive]
    change k • (q + direction - q) + q = q + k • direction
    rw [add_sub_cancel_left, add_comm]
  have image := image_segment ℝ A a b
  rw [value a nonnegative, value b (nonnegative.trans (member.1.trans member.2))] at image
  exact image.subset ⟨h, (segment_eq_Icc (member.1.trans member.2)).symm ▸ member,
    value h (nonnegative.trans member.1)⟩

theorem enclosingStrip_upper_physical_mem_segment (q : Plane) {a h b : ℝ}
    (nonnegative : 0 ≤ a) (member : h ∈ Set.Icc a b) :
    q + B.place.symm (B.enclosingStrip.upper.point h) ∈ segment ℝ
      (q + B.place.symm (B.enclosingStrip.upper.point a))
      (q + B.place.symm (B.enclosingStrip.upper.point b)) := by
  let direction := ((B.place u).re + (B.place u).im)⁻¹ • u
  let A : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap q (q + direction)
  have value (k : ℝ) (positive : 0 ≤ k) :
      A k = q + B.place.symm (B.enclosingStrip.upper.point k) := by
    rw [B.enclosingStrip_upper_point_ray positive]
    change k • (q + direction - q) + q = q + k • direction
    rw [add_sub_cancel_left, add_comm]
  have image := image_segment ℝ A a b
  rw [value a nonnegative, value b (nonnegative.trans (member.1.trans member.2))] at image
  exact image.subset ⟨h, (segment_eq_Icc (member.1.trans member.2)).symm ▸ member,
    value h (nonnegative.trans member.1)⟩

theorem enclosingStrip_lower_point_smul {a h : ℝ} (nonnegative : 0 ≤ a) (forward : 0 ≤ h) :
    B.enclosingStrip.lower.point (a * h) = a • B.enclosingStrip.lower.point h := by
  apply B.place.symm.injective
  rw [B.enclosingStrip_lower_point_ray (mul_nonneg nonnegative forward), map_smul,
    B.enclosingStrip_lower_point_ray forward]
  simp only [smul_smul, mul_assoc]

theorem enclosingStrip_upper_point_smul {a h : ℝ} (nonnegative : 0 ≤ a) (forward : 0 ≤ h) :
    B.enclosingStrip.upper.point (a * h) = a • B.enclosingStrip.upper.point h := by
  apply B.place.symm.injective
  rw [B.enclosingStrip_upper_point_ray (mul_nonneg nonnegative forward), map_smul,
    B.enclosingStrip_upper_point_ray forward]
  simp only [smul_smul, mul_assoc]

theorem enclosingStrip_lower_point_of_pos_scale {x y : Plane} {a h : ℝ}
    (positive : 0 < a) (height_positive : 0 < h)
    (on_bank : B.place y = B.enclosingStrip.lower.point h) (scale : x = a • y) :
    0 < (B.place x).re + (B.place x).im ∧
      B.place x = B.enclosingStrip.lower.point ((B.place x).re + (B.place x).im) := by
  have mapped : B.place x = a • B.enclosingStrip.lower.point h := by
    rw [scale, map_smul, on_bank]
  have height : (B.place x).re + (B.place x).im = a * h := by
    rw [mapped]
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
    rw [← mul_add, B.enclosingStrip.lower.point_height]
  refine ⟨by rw [height]; exact mul_pos positive height_positive, ?_⟩
  rw [height, B.enclosingStrip_lower_point_smul positive.le height_positive.le]
  exact mapped

theorem enclosingStrip_upper_point_of_pos_scale {x y : Plane} {a h : ℝ}
    (positive : 0 < a) (height_positive : 0 < h)
    (on_bank : B.place y = B.enclosingStrip.upper.point h) (scale : x = a • y) :
    0 < (B.place x).re + (B.place x).im ∧
      B.place x = B.enclosingStrip.upper.point ((B.place x).re + (B.place x).im) := by
  have mapped : B.place x = a • B.enclosingStrip.upper.point h := by
    rw [scale, map_smul, on_bank]
  have height : (B.place x).re + (B.place x).im = a * h := by
    rw [mapped]
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
    rw [← mul_add, B.enclosingStrip.upper.point_height]
  refine ⟨by rw [height]; exact mul_pos positive height_positive, ?_⟩
  rw [height, B.enclosingStrip_upper_point_smul positive.le height_positive.le]
  exact mapped

end Unfoldings.AcuteWedgeFrame
