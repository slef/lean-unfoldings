module

public import Unfoldings.Cap.GeometricSectorBankPoints
public import Unfoldings.Geometry.RayStripBankOrder
public import Unfoldings.Geometry.WedgeRotationFrame
public import Unfoldings.Geometry.RadialTailComponentRays

/-! The named enclosing banks identify a common radial component across adjacent sectors. -/

@[expose] public section

noncomputable section

namespace Unfoldings

namespace AcuteWedgeFrame

variable {u v : Plane} (B : AcuteWedgeFrame u v)

theorem enclosingStrip_lower_point_ray {h : ℝ} (nonnegative : 0 ≤ h) :
    B.place.symm (B.enclosingStrip.lower.point h) =
      h • (((B.place v).re + (B.place v).im)⁻¹ • v) := by
  have first := B.quadrant_self (x := u) ⟨1, 0, by norm_num, le_rfl, by simp⟩ B.first_ne
  have last := B.quadrant_self (x := v) ⟨0, 1, le_rfl, by norm_num, by simp⟩ B.last_ne
  change B.place.symm ((MonotoneStrip.rayStrip (B.place u) (B.place v)
    first.1 first.2 last.1 last.2).lower.point h) = _
  rw [MonotoneStrip.rayStrip_lower_point_eq_last _ _ _ _ _ _ nonnegative B.banks_cross_nonneg,
    MonotoneHeightGraph.ray_point_eq_smul, map_smul, map_smul, B.place.symm_apply_apply]

theorem enclosingStrip_upper_point_ray {h : ℝ} (nonnegative : 0 ≤ h) :
    B.place.symm (B.enclosingStrip.upper.point h) =
      h • (((B.place u).re + (B.place u).im)⁻¹ • u) := by
  have first := B.quadrant_self (x := u) ⟨1, 0, by norm_num, le_rfl, by simp⟩ B.first_ne
  have last := B.quadrant_self (x := v) ⟨0, 1, le_rfl, by norm_num, by simp⟩ B.last_ne
  change B.place.symm ((MonotoneStrip.rayStrip (B.place u) (B.place v)
    first.1 first.2 last.1 last.2).upper.point h) = _
  rw [MonotoneStrip.rayStrip_upper_point_eq_first _ _ _ _ _ _ nonnegative B.banks_cross_nonneg,
    MonotoneHeightGraph.ray_point_eq_smul, map_smul, map_smul, B.place.symm_apply_apply]

theorem enclosingStrip_lower_point_on_last_ray {h : ℝ} (positive : 0 < h) :
    ∃ a : ℝ, 0 < a ∧ B.place.symm (B.enclosingStrip.lower.point h) = a • v := by
  have quadrant := B.quadrant_self (x := v) ⟨0, 1, le_rfl, by norm_num, by simp⟩ B.last_ne
  refine ⟨h * ((B.place v).re + (B.place v).im)⁻¹,
    mul_pos positive (inv_pos.mpr (add_pos quadrant.1 quadrant.2)), ?_⟩
  rw [B.enclosingStrip_lower_point_ray positive.le, smul_smul]

theorem enclosingStrip_upper_point_on_first_ray {h : ℝ} (positive : 0 < h) :
    ∃ a : ℝ, 0 < a ∧ B.place.symm (B.enclosingStrip.upper.point h) = a • u := by
  have quadrant := B.quadrant_self (x := u) ⟨1, 0, by norm_num, le_rfl, by simp⟩ B.first_ne
  refine ⟨h * ((B.place u).re + (B.place u).im)⁻¹,
    mul_pos positive (inv_pos.mpr (add_pos quadrant.1 quadrant.2)), ?_⟩
  rw [B.enclosingStrip_upper_point_ray positive.le, smul_smul]

end AcuteWedgeFrame

namespace ConvexCap.SkirtTailFamily

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} {q : Plane} (F : K.SkirtTailFamily Z q)

theorem component_eq_of_pos_scaled_positions (lower : Z < 0)
    {c d : F.Component} {x y : Plane}
    (first : x ∈ (F.componentTail c).carrier) (last : y ∈ (F.componentTail d).carrier)
    {a : ℝ} (positive : 0 < a) (scale : y - q = a • (x - q)) : c = d := by
  let := F.finite
  exact RadialTailFamily.component_eq_of_pos_scaled_positions F.tail (K.convex_clipFootprint Z)
    (K.original_footprint_in_clip_interior lower (interior_subset F.origin))
    first last positive scale

/-- Boundary terminals may have different coordinates and different physical
heights. A shared named sector ray still identifies their actual component. -/
theorem component_eq_on_shared_sector_bank {t : ℝ} (positive : 0 < t) (small : t < 1)
    (lower : Z < 0) {i j : FiveSector}
    (shared : fiveSectorFirst t i = fiveSectorLast t j)
    {c d : F.Component} {x y : Plane} {a b : ℝ} (apositive : 0 < a) (bpositive : 0 < b)
    (first : x ∈ (F.componentTail c).carrier) (last : y ∈ (F.componentTail d).carrier)
    (first_bank : (fiveSectorFrame t positive small i).place (x - q) =
      (fiveSectorFrame t positive small i).enclosingStrip.upper.point a)
    (last_bank : (fiveSectorFrame t positive small j).place (y - q) =
      (fiveSectorFrame t positive small j).enclosingStrip.lower.point b) : c = d := by
  obtain ⟨s, spos, first_ray⟩ :=
    (fiveSectorFrame t positive small i).enclosingStrip_upper_point_on_first_ray apositive
  obtain ⟨r, rpos, last_ray⟩ :=
    (fiveSectorFrame t positive small j).enclosingStrip_lower_point_on_last_ray bpositive
  rw [← first_bank, LinearIsometryEquiv.symm_apply_apply] at first_ray
  rw [← last_bank, LinearIsometryEquiv.symm_apply_apply] at last_ray
  apply F.component_eq_of_pos_scaled_positions lower first last (div_pos rpos spos)
  rw [first_ray, last_ray, shared, smul_smul, div_mul_cancel₀ _ spos.ne']

end ConvexCap.SkirtTailFamily
end Unfoldings
