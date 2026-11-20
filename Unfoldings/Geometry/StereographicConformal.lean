module

public import Unfoldings.Geometry.StereographicJacobian
public import Unfoldings.Geometry.StereographicChord
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-! The centered chart is conformal, with exact local length scale. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Cap

open Filter Set InnerProductGeometry
open scoped Topology

/-- The differential of the inverse stereographic chart. -/
def inverseStereographicDerivative (x : Plane) : Plane →L[ℝ] Space :=
  (radialStereographicDerivative (northLift x)).comp horizontalLiftIsometry.toContinuousLinearMap

theorem hasFDerivAt_inverseStereographic (x : Plane) :
    HasFDerivAt inverseStereographic (inverseStereographicDerivative x) x := by
  let lift := horizontalLiftIsometry.toContinuousLinearMap
  have heq (p : Plane) : lift p + northLift 0 = northLift p := by
    ext i
    fin_cases i <;> simp [lift, horizontalLiftIsometry, horizontalLift, northLift]
  have l : HasFDerivAt (fun p : Plane => lift p + northLift 0) lift x :=
    lift.hasFDerivAt.add_const (northLift 0)
  rw [show (fun p : Plane => lift p + northLift 0) = northLift from funext heq] at l
  have d := (hasFDerivAt_radialStereographic (northLift x)).comp x l
  have eq : radialStereographic ∘ northLift = inverseStereographic := by
    funext p
    simp [radialStereographic]
  rw [eq] at d
  exact d

/-- The exact infinitesimal length scale is independent of tangent direction. -/
theorem norm_inverseStereographicDerivative (x u : Plane) :
    ‖inverseStereographicDerivative x u‖ = (2 / (1 + ‖x‖ ^ 2)) * ‖u‖ := by
  let f : ℝ → Space := fun t => inverseStereographic (x + t • u)
  have h : HasDerivAt f (inverseStereographicDerivative x u) 0 := by
    have line : HasDerivAt (fun t : ℝ => x + t • u) u 0 := by
      simpa only [id_eq, one_smul] using
        (HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) u).const_add x
    have line0 : x + (0 : ℝ) • u = x := by simp
    have d := hasFDerivAt_inverseStereographic x
    have d' := d.comp_hasDerivAt_of_eq 0 line line0.symm
    simpa only [f, Function.comp_def] using d'
  let slopeNormSq : ℝ → ℝ := fun t => ‖t⁻¹ • (f (0 + t) - f 0)‖ ^ 2
  have l : Tendsto slopeNormSq (𝓝[≠] (0 : ℝ)) (𝓝 (‖inverseStereographicDerivative x u‖ ^ 2)) :=
    h.tendsto_slope_zero.norm.pow 2
  let g : ℝ → ℝ := fun t =>
    4 * ‖u‖ ^ 2 / ((1 + ‖x + t • u‖ ^ 2) * (1 + ‖x‖ ^ 2))
  have l' : Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 (g 0)) := by
    have continuous : ContinuousAt g 0 := by
      dsimp [g]
      fun_prop (disch := positivity)
    exact continuous.continuousWithinAt
  have same : slopeNormSq =ᶠ[𝓝[≠] (0 : ℝ)] g := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have tne : t ≠ 0 := by simpa using ht
    have eq : x + t • u - (x + (0 : ℝ) • u) = t • u := by simp
    simp only [slopeNormSq, g, f, zero_add, norm_smul, mul_pow, inverseStereographic_chord_sq,
      eq, norm_smul, mul_pow]
    simp only [zero_smul, add_zero]
    have cancel : ‖t⁻¹‖ ^ 2 * ‖t‖ ^ 2 = 1 := by
      rw [← mul_pow, ← norm_mul, inv_mul_cancel₀ tne, norm_one, one_pow]
    rw [← mul_div_assoc]
    rw [show ‖t⁻¹‖ ^ 2 * (4 * (‖t‖ ^ 2 * ‖u‖ ^ 2)) =
      4 * ‖u‖ ^ 2 * (‖t⁻¹‖ ^ 2 * ‖t‖ ^ 2) by ring, cancel, mul_one]
  have sq := tendsto_nhds_unique l (l'.congr' same.symm)
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [sq]
  simp only [g, zero_smul, add_zero, mul_pow, div_pow, ← pow_two (1 + ‖x‖ ^ 2)]
  norm_num
  ring

/-- Conformality identifies each planar corner angle with its spherical tangent angle. -/
theorem angle_inverseStereographicDerivative (x u v : Plane) :
    angle (inverseStereographicDerivative x u) (inverseStereographicDerivative x v) =
      angle u v := by
  let c := 2 / (1 + ‖x‖ ^ 2)
  have c_pos : 0 < c := by dsimp [c]; positivity
  let f : Plane →ₗᵢ[ℝ] Space :=
    { (c⁻¹ • (inverseStereographicDerivative x).toLinearMap) with
      norm_map' := fun w => by
        change ‖c⁻¹ • inverseStereographicDerivative x w‖ = ‖w‖
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr c_pos.le),
          norm_inverseStereographicDerivative]
        change c⁻¹ * (c * ‖w‖) = ‖w‖
        rw [← mul_assoc, inv_mul_cancel₀ c_pos.ne', one_mul] }
  have scale (w : Plane) : inverseStereographicDerivative x w = c • f w := by
    change _ = c • (c⁻¹ • inverseStereographicDerivative x w)
    rw [smul_smul, mul_inv_cancel₀ c_pos.ne', one_smul]
  rw [scale u, scale v, angle_smul_left_of_pos _ _ c_pos, angle_smul_right_of_pos _ _ c_pos]
  exact f.angle_map u v

end Unfoldings.Cap
