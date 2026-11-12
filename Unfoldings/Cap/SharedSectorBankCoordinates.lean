module

public import Unfoldings.Cap.EnclosingBankSegments

/-! A shared physical sector bank has exact positive height coordinates in either frame. -/

@[expose] public section

namespace Unfoldings

namespace AcuteWedgeFrame

variable {u v : Plane} (B : AcuteWedgeFrame u v)

theorem enclosingStrip_upper_point_of_pos_smul_first {a : ℝ} (positive : 0 < a) :
    0 < (B.place (a • u)).re + (B.place (a • u)).im ∧
      B.place (a • u) = B.enclosingStrip.upper.point
        ((B.place (a • u)).re + (B.place (a • u)).im) := by
  have quadrant := B.quadrant_self (x := u) ⟨1, 0, by norm_num, le_rfl, by simp⟩ B.first_ne
  have height : 0 < (B.place u).re + (B.place u).im := add_pos quadrant.1 quadrant.2
  have at_first : B.place u = B.enclosingStrip.upper.point ((B.place u).re + (B.place u).im) := by
    apply B.place.symm.injective
    rw [B.place.symm_apply_apply, B.enclosingStrip_upper_point_ray height.le, smul_smul,
      mul_inv_cancel₀ height.ne', one_smul]
  exact B.enclosingStrip_upper_point_of_pos_scale positive height at_first rfl

theorem enclosingStrip_lower_point_of_pos_smul_last {a : ℝ} (positive : 0 < a) :
    0 < (B.place (a • v)).re + (B.place (a • v)).im ∧
      B.place (a • v) = B.enclosingStrip.lower.point
        ((B.place (a • v)).re + (B.place (a • v)).im) := by
  have quadrant := B.quadrant_self (x := v) ⟨0, 1, le_rfl, by norm_num, by simp⟩ B.last_ne
  have height : 0 < (B.place v).re + (B.place v).im := add_pos quadrant.1 quadrant.2
  have at_last : B.place v = B.enclosingStrip.lower.point ((B.place v).re + (B.place v).im) := by
    apply B.place.symm.injective
    rw [B.place.symm_apply_apply, B.enclosingStrip_lower_point_ray height.le, smul_smul,
      mul_inv_cancel₀ height.ne', one_smul]
  exact B.enclosingStrip_lower_point_of_pos_scale positive height at_last rfl

end AcuteWedgeFrame

theorem fiveSector_shared_lower_to_upper_coordinates {t : ℝ} (positive : 0 < t) (small : t < 1)
    {i j : FiveSector} (shared : fiveSectorFirst t i = fiveSectorLast t j)
    {h : ℝ} (height_positive : 0 < h) :
    let z := (fiveSectorFrame t positive small i).place
      ((fiveSectorFrame t positive small j).place.symm
        ((fiveSectorFrame t positive small j).enclosingStrip.lower.point h))
    0 < z.re + z.im ∧
      z = (fiveSectorFrame t positive small i).enclosingStrip.upper.point (z.re + z.im) := by
  obtain ⟨a, apositive, ray⟩ :=
    (fiveSectorFrame t positive small j).enclosingStrip_lower_point_on_last_ray height_positive
  conv_rhs at ray => rw [← shared]
  have result := (fiveSectorFrame t positive small i).enclosingStrip_upper_point_of_pos_smul_first
    apositive
  rwa [← ray] at result

theorem fiveSector_shared_upper_to_lower_coordinates {t : ℝ} (positive : 0 < t) (small : t < 1)
    {i j : FiveSector} (shared : fiveSectorFirst t i = fiveSectorLast t j)
    {h : ℝ} (height_positive : 0 < h) :
    let z := (fiveSectorFrame t positive small j).place
      ((fiveSectorFrame t positive small i).place.symm
        ((fiveSectorFrame t positive small i).enclosingStrip.upper.point h))
    0 < z.re + z.im ∧
      z = (fiveSectorFrame t positive small j).enclosingStrip.lower.point (z.re + z.im) := by
  obtain ⟨a, apositive, ray⟩ :=
    (fiveSectorFrame t positive small i).enclosingStrip_upper_point_on_first_ray height_positive
  conv_rhs at ray => rw [shared]
  have result := (fiveSectorFrame t positive small j).enclosingStrip_lower_point_of_pos_smul_last
    apositive
  rwa [← ray] at result

end Unfoldings
