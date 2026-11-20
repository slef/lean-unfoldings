module

public import Unfoldings.Geometry.StereographicArea
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! A radial equal-area map gives the sharp area lower bound on star-shaped
regions without a boundary regularity assumption. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open MeasureTheory
open scoped Pointwise ENNReal

/-- This radial planar map has Jacobian equal to the stereographic area density. -/
def stereographicAreaMap (x : Plane) : Plane := (2 * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹) • x

def stereographicAreaMapDerivative (x : Plane) : Plane →L[ℝ] Plane :=
  let d := Real.sqrt (1 + ‖x‖ ^ 2)
  (2 * d⁻¹) • ContinuousLinearMap.id ℝ Plane +
    ((-2 / d ^ 3) • innerSL ℝ x).smulRight x

theorem hasFDerivAt_stereographicAreaMap (x : Plane) :
    HasFDerivAt stereographicAreaMap (stereographicAreaMapDerivative x) x := by
  let d := Real.sqrt (1 + ‖x‖ ^ 2)
  have positive : 0 < d := Real.sqrt_pos.2 (by positivity)
  have hNorm := (hasFDerivAt_id x).norm_sq
  have den : HasFDerivAt (fun y : Plane => 1 + ‖y‖ ^ 2) (2 • innerSL ℝ x) x := by
    have h := (hasFDerivAt_const (1 : ℝ) x).add hNorm
    rw [zero_add, ContinuousLinearMap.comp_id] at h
    exact h
  have root := den.sqrt (show 1 + ‖x‖ ^ 2 ≠ 0 by positivity)
  have inv := ((hasFDerivAt_inv positive.ne').comp x root).const_smul (2 : ℝ)
  have scale : HasFDerivAt (fun y : Plane => 2 * (Real.sqrt (1 + ‖y‖ ^ 2))⁻¹)
      ((-2 / d ^ 3) • innerSL ℝ x) x := by
    have same : (-2 / d ^ 3) • innerSL ℝ x =
        (2 : ℝ) • ((ContinuousLinearMap.toSpanSingleton ℝ (-(d ^ 2)⁻¹)).comp
          ((1 / (2 * d)) • (2 • innerSL ℝ x))) := by
      ext y
      simp only [smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
      field_simp [positive.ne']
      ring
    rw [same]
    exact inv
  exact scale.smul (hasFDerivAt_id x)

theorem det_stereographicAreaMapDerivative (x : Plane) :
    (stereographicAreaMapDerivative x).det = 4 / (1 + ‖x‖ ^ 2) ^ 2 := by
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  let d := Real.sqrt (1 + ‖x‖ ^ 2)
  have positive : 0 < d := Real.sqrt_pos.2 (by positivity)
  have sq : d ^ 2 = 1 + ‖x‖ ^ 2 := Real.sq_sqrt (by positivity)
  have coordSq : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  change LinearMap.det (stereographicAreaMapDerivative x).toLinearMap = _
  rw [← sq, ← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp [b, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    stereographicAreaMapDerivative, ← show d = Real.sqrt (1 + ‖x‖ ^ 2) from rfl,
    PiLp.inner_apply, EuclideanSpace.single,
    PiLp.single_apply]
  field_simp [positive.ne']
  linear_combination 4 * d ^ 2 * (sq.trans (congrArg (fun t : ℝ => 1 + t) coordSq))

theorem stereographicAreaMap_injective : Function.Injective stereographicAreaMap := by
  intro x y eq
  have norms (z : Plane) : ‖stereographicAreaMap z‖ ^ 2 = 4 * ‖z‖ ^ 2 / (1 + ‖z‖ ^ 2) := by
    have root : 0 < Real.sqrt (1 + ‖z‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
    rw [stereographicAreaMap, norm_smul, Real.norm_of_nonneg (by positivity), mul_pow, mul_pow,
      inv_pow, Real.sq_sqrt (by positivity)]
    ring
  have distSq := congrArg (fun z : Plane => ‖z‖ ^ 2) eq
  rw [norms, norms] at distSq
  have square : ‖x‖ ^ 2 = ‖y‖ ^ 2 := by
    have left : 1 + ‖x‖ ^ 2 ≠ 0 := by positivity
    have right : 1 + ‖y‖ ^ 2 ≠ 0 := by positivity
    field_simp [left, right] at distSq
    linarith only [distSq]
  rw [stereographicAreaMap, stereographicAreaMap, square] at eq
  exact smul_right_injective Plane (by positivity) eq

/-- A compact chart region has spherical area equal to the area of the radial
equal-area image. -/
theorem solidAngle_eq_volume_stereographicAreaMap {s : Set Plane} (compact : IsCompact s) :
    solidAngleMeasure (inverseStereographic '' s) = volume (stereographicAreaMap '' s) := by
  rw [solidAngle_inverseStereographic_image compact]
  have jac := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure Plane)
    compact.measurableSet (fun x _ => (hasFDerivAt_stereographicAreaMap x).hasFDerivWithinAt)
    stereographicAreaMap_injective.injOn (fun _ => 1)
  have positive (x : Plane) : 0 ≤ 4 / (1 + ‖x‖ ^ 2) ^ 2 := by positivity
  simpa only [lintegral_const, Measure.restrict_apply_univ, one_mul, mul_one,
    det_stereographicAreaMapDerivative, abs_of_nonneg (positive _), stereographicDensity]
    using jac.symm

/-- The area lower bound retains the actual chart radius. In particular radius
one gives the global factor two in the spherical two-side estimate. -/
theorem stereographic_area_lower {s : Set Plane} (compact : IsCompact s)
    (star : StarConvex ℝ (0 : Plane) s) {R : ℝ} (nonneg : 0 ≤ R)
    (radius : ∀ x ∈ s, ‖x‖ ≤ R) :
    ENNReal.ofReal (4 / (1 + R ^ 2)) * volume s ≤
      solidAngleMeasure (inverseStereographic '' s) := by
  let c := 2 * (Real.sqrt (1 + R ^ 2))⁻¹
  have c_positive : 0 < c := by dsimp [c]; positivity
  have included : c • s ⊆ stereographicAreaMap '' s := by
    rintro _ ⟨x, hx, rfl⟩
    have sq := (sq_le_sq₀ (norm_nonneg x) nonneg).2 (radius x hx)
    let d := Real.sqrt (1 + R ^ 2 - ‖x‖ ^ 2)
    have one_le : 1 ≤ d := by
      change 1 ≤ Real.sqrt (1 + R ^ 2 - ‖x‖ ^ 2)
      exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
    have d_positive : 0 < d := zero_lt_one.trans_le one_le
    have d_sq : d ^ 2 = 1 + R ^ 2 - ‖x‖ ^ 2 := Real.sq_sqrt (by linarith)
    let y := d⁻¹ • x
    have t_nonneg : 0 ≤ d⁻¹ := inv_nonneg.2 d_positive.le
    have t_small : d⁻¹ ≤ 1 := inv_le_one_of_one_le₀ one_le
    have y_in : y ∈ s := by
      have h := star hx (sub_nonneg.mpr t_small) t_nonneg
        (sub_add_cancel (1 : ℝ) d⁻¹)
      simpa only [smul_zero, zero_add, y] using h
    refine ⟨y, y_in, ?_⟩
    have norm_y : ‖y‖ ^ 2 = d⁻¹ ^ 2 * ‖x‖ ^ 2 := by
      change ‖d⁻¹ • x‖ ^ 2 = _
      rw [norm_smul, Real.norm_of_nonneg t_nonneg, mul_pow]
    have factor : Real.sqrt (1 + ‖y‖ ^ 2) * d = Real.sqrt (1 + R ^ 2) := by
      apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
      rw [mul_pow, Real.sq_sqrt (show 0 ≤ 1 + ‖y‖ ^ 2 by positivity),
        Real.sq_sqrt (show 0 ≤ 1 + R ^ 2 by positivity), norm_y]
      calc
        _ = d ^ 2 + ‖x‖ ^ 2 := by field_simp [d_positive.ne']
        _ = _ := by linarith only [d_sq]
    rw [stereographicAreaMap]
    change (2 * (Real.sqrt (1 + ‖y‖ ^ 2))⁻¹) • (d⁻¹ • x) = c • x
    rw [smul_smul, mul_assoc, ← mul_inv, factor]
  have scale : volume (c • s) = ENNReal.ofReal (4 / (1 + R ^ 2)) * volume s := by
    rw [Measure.addHaar_smul_of_nonneg volume c_positive.le,
      show Module.finrank ℝ Plane = 2 by simp [Plane]]
    have eq : c ^ 2 = 4 / (1 + R ^ 2) := by
      dsimp [c]
      rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
      ring
    rw [eq]
  rw [solidAngle_eq_volume_stereographicAreaMap compact, ← scale]
  exact measure_mono included

/-- If the spherical region is within angle `d` of the chart center, its solid
angle is at least `4 cos²(d/2)` times its projected area. -/
theorem stereographic_area_lower_of_angle {s : Set Plane} (compact : IsCompact s)
    (star : StarConvex ℝ (0 : Plane) s) {d : ℝ} (hd : d < Real.pi / 2)
    (radius : ∀ x ∈ s, InnerProductGeometry.angle (northLift 0) (inverseStereographic x) ≤ d) :
    ENNReal.ofReal (4 * Real.cos (d / 2) ^ 2) * volume s ≤
      solidAngleMeasure (inverseStereographic '' s) := by
  by_cases hd0 : 0 ≤ d
  · let c := Real.cos d
    have c_pos : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hd⟩
    have sum_pos : 0 < 1 + c := by linarith
    have ratio0 : 0 ≤ (1 - c) / (1 + c) :=
      div_nonneg (sub_nonneg.mpr (Real.cos_le_one d)) sum_pos.le
    let R := Real.sqrt ((1 - c) / (1 + c))
    have R_sq : R ^ 2 = (1 - c) / (1 + c) := Real.sq_sqrt ratio0
    have R_nonneg : 0 ≤ R := Real.sqrt_nonneg _
    have planar_radius (x) (hx : x ∈ s) : ‖x‖ ≤ R := by
      have hcos : c ≤
          Real.cos (InnerProductGeometry.angle (northLift 0) (inverseStereographic x)) :=
        Real.cos_le_cos_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg _ _)
          (by linarith [Real.pi_pos]) (radius x hx)
      have inner := InnerProductGeometry.cos_angle_mul_norm_mul_norm (northLift 0)
        (inverseStereographic x)
      rw [northLift_zero_unit, inverseStereographic_unit, mul_one, mul_one,
        horizontal_inner, northLift_horizontal, northLift_height,
        inner_zero_left, one_mul, zero_add,
        inverseStereographic_height] at inner
      rw [inner] at hcos
      have h := (le_div_iff₀ (show 0 < 1 + ‖x‖ ^ 2 by positivity)).mp hcos
      apply (sq_le_sq₀ (norm_nonneg _) R_nonneg).mp
      rw [R_sq]
      apply (le_div_iff₀ sum_pos).mpr
      nlinarith only [h]
    have scale : 4 / (1 + R ^ 2) = 4 * Real.cos (d / 2) ^ 2 := by
      have cos := Real.cos_two_mul (d / 2)
      rw [show 2 * (d / 2) = d by ring] at cos
      calc
        _ = 2 * (1 + c) := by
          rw [R_sq]
          have den : 0 < 1 + (1 - c) / (1 + c) := by linarith
          field_simp [sum_pos.ne', den.ne']
          ring
        _ = _ := by dsimp [c]; linarith only [cos]
    rw [← scale]
    exact stereographic_area_lower compact star R_nonneg planar_radius
  · have empty : s = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
      hd0 ((InnerProductGeometry.angle_nonneg _ _).trans (radius x hx))
    simp [empty]

end Unfoldings.Cap
