module

public import Unfoldings.FewestNets.RevisedLatitudeAnnularBudget
public import Unfoldings.Cap.SharpGnomonicSolidAngle

/-! The actual cell and pole triangle fit in the revised area budget. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.RevisedLatitudeGrid

open Real Cap MeasureTheory
open scoped ENNReal

variable {a : ℝ} {positive : 0 < a} {small : a ≤ π / 6} {i : AnnularTriangle a}
  (D : AnnularChartData positive small i)

theorem AnnularChartData.affine_height_upper :
    D.height ≤ radius a * (relativeStep a / 0.9612 +
      ordinateErrorFactor (isPolarStrip a i.1.val) * 0.268 ^ 2) := by
  let E := ordinateErrorFactor (isPolarStrip a i.1.val)
  let d := rowStep a
  let r := radius a
  let b := spacing a
  have e : E * b ^ 2 / r ≤ (E * 0.268 ^ 2) * r := by
    apply (div_le_iff₀ (radius_pos positive)).mpr
    have sq : b ^ 2 ≤ (0.268 * r) ^ 2 :=
      pow_le_pow_left₀ (spacing_pos positive).le (spacing_lt positive small).le 2
    have ep : 0 ≤ E := ordinateErrorFactor_nonneg (isPolarStrip a i.1.val)
    nlinarith only [mul_le_mul_of_nonneg_left sq ep]
  have h := D.height_upper
  change D.height ≤ 2 * sin (d / 2) / 0.9612 + E * b ^ 2 / r at h
  have sine := div_le_div_of_nonneg_right (sin_le (half_pos (rowStep_pos positive small)).le)
    (show (0 : ℝ) ≤ 0.9612 by norm_num)
  change sin (d / 2) / 0.9612 ≤ d / 2 / 0.9612 at sine
  have q : relativeStep a * r = d := rowStep_eq_relativeStep_mul_radius positive
  change D.height ≤ r * (relativeStep a / 0.9612 + E * 0.268 ^ 2)
  ring_nf at h sine e q ⊢
  linarith only [h, sine, e, q]

/-- The reoriented actual triangle contains the normals used by routing, and
its solid angle plus the determinant bound for any pole triangle is at most
the area portion of the routing allowance. -/
theorem AnnularChartData.area_budget :
    let S := latitudeSlopeTriangle (-D.halfBase) D.halfBase D.base D.apex D.height
    (solidAngleMeasure (gnomonicNormal '' S)).toReal +
        (spacing a / (2 * 0.9612)) * ordinateBound a (isPolarStrip a i.1.val) ≤
      a ^ 2 * areaFactor (isPolarStrip a i.1.val) (relativeStep a) := by
  let S := latitudeSlopeTriangle (-D.halfBase) D.halfBase D.base D.apex D.height
  let x := relativeStep a
  let r := radius a
  let b := spacing a
  let E := ordinateErrorFactor (isPolarStrip a i.1.val)
  have base : -D.halfBase ≤ D.halfBase := (neg_lt_self D.base_pos).le
  have width : D.halfBase - (-D.halfBase) = 2 * D.halfBase := by ring
  have vol : volume S = ENNReal.ofReal (2 * D.halfBase * D.height / 2) := by
    rw [show S = _ from rfl, volume_latitudeSlopeTriangle base D.height_pos, width]
  have bound := Cap.solidAngle_gnomonic_le_volume
    (isCompact_latitudeSlopeTriangle (-D.halfBase) D.halfBase D.base D.apex D.height)
  change solidAngleMeasure (gnomonicNormal '' S) ≤ volume S at bound
  rw [vol] at bound
  have measure := ENNReal.toReal_mono ENNReal.ofReal_ne_top bound
  rw [ENNReal.toReal_ofReal (by have := D.base_pos; have := D.height_pos; positivity : 0 ≤ 2 * D.halfBase * D.height / 2)] at measure
  have maxheight : D.height ≤ r * (x / 0.9612 + E * 0.268 ^ 2) := D.affine_height_upper
  have width_le : 2 * D.halfBase ≤ b / 0.9612 := D.base_upper.le
  have product := mul_le_mul width_le maxheight D.height_pos.le
    (div_nonneg (spacing_pos positive).le (by norm_num))
  change (solidAngleMeasure (gnomonicNormal '' S)).toReal +
    (b / (2 * 0.9612)) * (r * (x / (2 * 0.9612) + E * 0.268 ^ 2)) ≤ _
  have square : r ^ 2 = 0.72 ^ 2 * a := by
    unfold r radius
    rw [mul_pow, sq_sqrt positive.le]
  have scale : b * r = 0.51 * (0.72 ^ 2) * a ^ 2 := by
    change (0.51 * a * r) * r = _
    rw [mul_assoc, ← pow_two, square]
    ring
  have eq :
      (b / 0.9612) * (r * (x / 0.9612 + E * 0.268 ^ 2)) / 2 +
        (b / (2 * 0.9612)) * (r * (x / (2 * 0.9612) + E * 0.268 ^ 2)) =
      a ^ 2 * areaFactor (isPolarStrip a i.1.val) (relativeStep a) := by
    unfold areaFactor
    change _ = a ^ 2 * (0.51 * 0.72 ^ 2 / (2 * 0.9612) *
      (3 * x / (2 * 0.9612) + 2 * E * 0.268 ^ 2))
    linear_combination ((3 * x / (2 * 0.9612) + 2 * E * 0.268 ^ 2) / (2 * 0.9612)) * scale
  linarith only [product, measure, eq]

/-- Half the determinant of any two chart slopes is at most the pole portion
of the area budget. -/
theorem AnnularChartData.pole_triangle_bound {p q : Plane}
    (hp : p ∈ latitudeSlopeTriangle (-D.halfBase) D.halfBase D.base D.apex D.height)
    (hq : q ∈ latitudeSlopeTriangle (-D.halfBase) D.halfBase D.base D.apex D.height) :
    |p 0 * q 1 - q 0 * p 1| / 2 ≤
      (spacing a / (2 * 0.9612)) * ordinateBound a (isPolarStrip a i.1.val) := by
  obtain ⟨px, py⟩ := D.coordinate_bounds hp
  obtain ⟨qx, qy⟩ := D.coordinate_bounds hq
  have l := mul_le_mul px qy (abs_nonneg _) ((abs_nonneg _).trans px)
  have r := mul_le_mul qx py (abs_nonneg _) ((abs_nonneg _).trans qx)
  have triangle := abs_sub (p 0 * q 1) (q 0 * p 1)
  rw [abs_mul, abs_mul] at triangle
  linarith only [l, r, triangle]

end Unfoldings.FewestNets.RevisedLatitudeGrid
